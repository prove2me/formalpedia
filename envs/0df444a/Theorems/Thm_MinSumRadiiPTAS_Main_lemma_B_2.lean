-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_lemma_B_2
-- name    : MinSumRadiiPTAS.Main.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:06:32.183022+00:00
-- url     : https://prove2.me/theorems/50d640e1-5c9c-4bc4-a88f-4c415cc53e3e
-- title:
--   Lemma B.2 — benchmark weight: $\mathbb E[w(O')] \le \mathrm{cost}(O)(1-\varepsilon/2) + \lambda|O|$ for $O = O_{3R}$
-- statement:
--   **Lemma B.2** (p. 37). In Case II on a normalised instance ($\varepsilon \in (0, 1/10)$, $\lambda \in [\varepsilon/k, 10k/\varepsilon]$, $\lambda < 6R$), after any terminated run of the preprocessing (leaving $P''$), let $O = O_{3R}$ be any optimal cover of $P''$ by balls of $\mathfrak B$ of radius $\le 3R$, and let $O'$ be the benchmark constructed from $O$ (§5.2.1 with the changes of §6.2 and Appendix B: $L = \lceil e^{7100}/\varepsilon\rceil$, $U = 2^{3L}$, target $3R$, certified balls $\mathcal C_R$, any admissible ordered nets $N_i$). Then $w(O')$ is a measurable function of the randomness and
--   $$\mathbb E[w(O')] \le \mathrm{cost}(O)\Big(1 - \frac\varepsilon2\Big) + \lambda|O|,$$
--   the expectation over the shift $\sigma$, the LDD radii of all levels and all FormGroups draws.
--
--   Differences from the source:
--   - encoding: point set P with |P| = n, a metric d on P → points Fin n (0-based), d : Fin n → Fin n → ℝ with the published MinSumClust.IsMetric (d(p,p)=0, d ≥ 0, symmetry, triangle inequality, d(p,q) > 0 for p ≠ q); reason: same instances
--   - reading: the lemma's own sentence (context of §6) → explicit hypotheses: StandingInstance d k ε (Lemma 2.1's normalisation: integer distances in [1, ⌈10k/ε⌉], opt ≤ 8k/ε, 1 ≤ k ≤ n), ε ∈ (0, 1/10), λ ∈ [ε/k, 10k/ε] (Theorem 6.1); reason: p. 7 assumes the normalisation for the rest of the paper, p. 6 fixes ε ∈ (0, 1/10), and §6 works under Theorem 6.1's λ; trap 19 (section standing assumptions are binders)
--   - reading: P″ and O_{3R} of §6.2 (Case II, λ < 6R) → P″ := preFinal of any terminated run of the preprocessing (IsPreprocessingRun) from any client set P′, O_{3R} any optimal cover of P″ by balls of 𝔅 of radius ≤ 3R (IsOptCover); reason: the paper's preprocessing picks dense balls in an arbitrary order and O_{3R} is any optimal solution; the statement holds for all of them
--   - encoding: E over σ, the radii ℓ_i and the FormGroups calls → lower Lebesgue integral of ofReal(w(O′)) under MinSumFPT.tapeLaw, every source read from its own tape coordinate (σ = min(L−1, ⌊Lu⌋), ℓ_i = a_i(8 + u), D = U + 1 + min(U−1, ⌊Uu⌋), permutations as orders of uniform priorities), with measurability of w(O′) as a conjunct; reason: each source has the paper's law and the sources are independent; w(O′) ≥ 0, so the lower integral of a measurable w(O′) is its expectation
--   - encoding: FormGroups randomness of every ComputeDP((X, i), S) call → one independent draw per node (X, i); reason: the benchmark uses only the call with S = S_{X,i}, so its law is unchanged
--   - reading: the net N_i computed by Net(Z_i, 6a_i) and LDD's "fixed but arbitrary order" → any ordered nets with NetsAdmissible (for each σ < L and level 1 ≤ i ≤ t a duplicate-free list of a 6a_i-net of Z_i); reason: the paper's greedy net and order are arbitrary; the statement holds for all of them
--   - generalization: p. 26 assumes R ≤ ⌈10k/ε⌉ without loss before the bounded-radius DP analysis → no upper bound on R beyond the Case II condition λ < 6R; reason: this includes every source instance. Above the maximum distance all minimal balls are allowed and no dense preprocessing ball exists; extra threshold levels have empty nets and only a far child. The algorithm can cap R and use Case I if needed
--   - generalization: Appendix B (p. 36) assumes P″ is nonempty after disposing of the empty case → P″ may be empty; reason: for P″ = ∅, positive λ forces O = ∅ and the constructed benchmark is empty, so both sides are zero; nonempty instances retain the complete source claim
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, Appendix B, Lemma B.2, p. 37 (benchmark §5.2.1 p. 19, changes pp. 26, 36–37)

import Mathlib
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumRadiiPTAS_Main_LP
import Definitions.Def_MinSumRadiiPTAS_Main_CaseII

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-- **Lemma B.2** (p. 37): in Case II on a normalised instance, after any terminated run of the
preprocessing (client set `P″`), let `O = O_{3R}` be any optimal cover of `P″` by balls of radius
`≤ 3R` and `O′` the benchmark built from `O` (§5.2.1 with the changes of §6.2 and Appendix B), for
any admissible choice of the ordered nets `N_i`. Then `E[w(O′)] ≤ cost(O)(1 − ε/2) + λ|O|`, the
expectation over the threshold shift `σ`, the LDD radii of all levels and all FormGroups draws (all
read from the random tape under `MinSumFPT.tapeLaw`); `w(O′)` is a measurable function of the tape. -/
theorem lemma_B_2 {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε lam R : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1 / 10) (hI : StandingInstance d k ε) (hlam1 : ε / k ≤ lam)
    (hlam2 : lam ≤ 10 * k / ε) (hcase : lam < 6 * R) (P1 : Finset (Fin n))
    (steps : List (Fin n × ℝ)) (hrun : IsPreprocessingRun d lam ε R P1 steps)
    (O3 : Finset (Ball n))
    (hO3 : IsOptCover d lam (fun B => B.radius ≤ 3 * R) (preFinal d R P1 steps) O3)
    (nets : ℕ → ℕ → List (Fin n))
    (hnets : (PipelineData.mk d lam ε R (preFinal d R P1 steps) O3 nets).NetsAdmissible) :
    let A : PipelineData n := ⟨d, lam, ε, R, preFinal d R P1 steps, O3, nets⟩
    Measurable (fun ω => A.weight ω (A.benchmark ω)) ∧
      ∫⁻ ω, ENNReal.ofReal (A.weight ω (A.benchmark ω)) ∂MinSumFPT.tapeLaw ≤
        ENNReal.ofReal (cost O3 * (1 - ε / 2) + lam * O3.card) := by sorry

end MinSumRadiiPTAS.Main
