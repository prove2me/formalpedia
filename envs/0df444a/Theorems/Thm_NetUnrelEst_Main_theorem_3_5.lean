-- Prove2me | Theorems.Thm_NetUnrelEst_Main_theorem_3_5
-- name    : NetUnrelEst.Main.theorem_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:16:24.313226+00:00
-- url     : https://prove2.me/theorems/74d2691f-2735-4f68-bee8-eb459d78095f
-- title:
--   Theorem 3.5 — E(U_j r_j) ≤ C_{g₀} u² e^{χ t_j} for the actual recursion with failing cut searches
-- statement:
--   Assume (25): the reduced input (connected, $n\ge2$, no loops, no parallel edges, $0<p_e<1$) satisfies $n^{-c_0}\le u\le 2/3$ and $\lambda\le c_0\log n$, $c_0=29/10$. Put $H=\log(8n)$, $\eta=1/(256H)$, $\ell=\log(1/u)$, and $\chi=\ell/2$ if $u\le n^{-1/8}$, $\chi=2\ell$ otherwise. Heavy edges ($w_e>86H$) are revealed first; $\mathcal H$ is the event that they all work. Every other edge is represented by $N_e$ parallel edges with the counts of §2.6, so it fails with probability $Z_e=\pi^{N_e}$.
--
--   For every $g_0>0$ there are $\omega_0>0$, $C_{g_0}$ and $n_1$ such that the following holds for every search error $0<\omega\le\omega_0$ and every input with $n\ge n_1$ satisfying (25). Take any time sequence fixed in advance with $\lambda(t_{j+1}-t_j)\le g_0$, and any cut search on the represented graph that always returns a cut of the current graph and returns a minimum one (in multiplicities) with probability at least $1-\omega$, using fresh randomness. Then the recursive estimate satisfies, at every level $j$ including time zero,
--   $$\mathbb E\big(U_jr_j\mid\mathcal H\big)\le C_{g_0}\,u^2e^{\chi t_j}.\tag{32}$$
--
--   Together with Lemma 2.2, (32) bounds the second moment of one recursive run by $O(u^2)$ when the contraction times grow at the right rate. It is the step that allows the cut searches to fail with constant probability.
--
--   **Formalization Note.** Conditioning on $\mathcal H$ is encoded by starting the recursion with the heavy edges already arrived (they work). The expectation averages first over the counts (a finite product law) and then over the extended random path of the recursion run with failure probabilities $Z_e$. The cut search is a law on cuts that may depend on the counts, the level, the arrived set and the stored cuts.
--
--   Differences from the source:
--   - reading: 'for sufficiently large n and a sufficiently small fixed search error ω > 0 depending only on g0', with C_{g0} → ∀ g0 > 0, ∃ ω₀ > 0, ∃ C, ∃ n₁, ∀ ω ∈ (0, ω₀], ∀ inputs with n ≥ n₁; reason: the reading Corollary 4.3 uses; the proof's constant C D/(1 − ωD) ≤ 2CD does not depend on ω once ωD ≤ 1/2
--   - encoding: expectations conditional on H, with the heavy edges revealed and contracted → the recursion and its path started with the heavy edges in the arrived set; reason: on H every heavy edge works, so it is contracted at time zero; the counts are independent of H
--   - encoding: the independently generated time sequence with λ(t_{j+1} − t_j) ≤ g ≤ g0 → every fixed sequence 0 = t₀ < ⋯ < t_h = 1 with λ(t_{j+1} − t_j) ≤ g0; reason: the bound is proved conditional on the sequence, which is independent of the representation
--   - encoding: a cut search that returns an actual cut and a minimum cut with conditional probability ≥ 1 − ω, fresh randomness per attempt → a law on cuts depending on the counts, the level, the arrived set and the stored cuts, supported on cuts of the current graph, giving mass ≥ 1 − ω to minimum cuts of the current graph for the multiplicities N_e; reason: the current represented graph is the arrived set with the multiplicities; fresh randomness is the law's independence from everything else
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 20, Theorem 3.5; standing assumptions p. 18, (25); p. 20, §3.4

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelEst_Main_CutSums
import Definitions.Def_NetUnrelEst_Main_Contraction
import Definitions.Def_NetUnrelEst_Main_Recursion

open scoped BigOperators ENNReal

open NetUnrelDesign.Main

namespace NetUnrelEst.Main

/-- **Theorem 3.5.** For every `g₀ > 0` there are `ω₀ > 0`, `C_{g₀}` and `n₁` such that: for every
search error `0 < ω ≤ ω₀`, every reduced input with `n ≥ n₁` satisfying (25)
(`n^{−c₀} ≤ u ≤ 2/3`, `λ ≤ c₀ log n`, `c₀ = 29/10`), every time sequence fixed in advance with
`λ(t_{j+1} − t_j) ≤ g₀`, and every cut search on the represented graph that always returns a cut
of the current graph and a minimum one (in multiplicities) with probability at least `1 − ω`
using fresh randomness: conditional on `H` (all heavy edges `w_e > 86H` work, `H = log(8n)`),
with light-edge counts for `η = 1/(256H)`, every level `j` satisfies
`E(U_j r_j) ≤ C_{g₀} u² e^{χ t_j}` (32), `χ = ℓ/2` for `u ≤ n^{−1/8}` and `χ = 2ℓ` otherwise,
`ℓ = log(1/u)`. Sun 2027, p. 20, Theorem 3.5. -/
theorem theorem_3_5 (g0 : ℝ) (hg0 : 0 < g0) :
    ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∃ C : ℝ, ∃ n₁ : ℕ, ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ →
      ∀ {n m : ℕ} (ends : Ends n m) (p : Fin m → ℝ), IsReduced ends p → n₁ ≤ n →
        (n : ℝ) ^ (-(29 / 10 : ℝ)) ≤ unrel ends p → unrel ends p ≤ 2 / 3 →
        lam ends p ≤ 29 / 10 * Real.log n →
        ∀ (h : ℕ) (t : ℕ → ℝ), TimeSeq h t → (∀ j < h, lam ends p * (t (j + 1) - t j) ≤ g0) →
        ∀ rule : Finset (Fin m) → CutRule n m,
          (∀ U, ValidRule ends (rule U)) →
          (∀ U j S A, ¬ OneVertex ends S →
            ENNReal.ofReal (1 - ω) ≤ (rule U j S A).toOuterMeasure
              {C | IsMinCurrentCut ends
                (fun e => (repCount (1 / (256 * Real.log (8 * n))) p U e : ℝ)) S C}) →
          ∀ j ≤ h,
            expect (fun e => if 86 * Real.log (8 * n) < wOf p e then 0
                else upProb (1 / (256 * Real.log (8 * n))) (p e))
              (fun U => pathMoment ends (repZ (1 / (256 * Real.log (8 * n))) p U) t (rule U)
                (Finset.univ.filter fun e => 86 * Real.log (8 * n) < wOf p e) j) ≤
            C * unrel ends p ^ 2 *
              Real.exp ((if unrel ends p ≤ (n : ℝ) ^ (-(1 / 8 : ℝ))
                then Real.log (1 / unrel ends p) / 2 else 2 * Real.log (1 / unrel ends p)) * t j) := by sorry

end NetUnrelEst.Main
