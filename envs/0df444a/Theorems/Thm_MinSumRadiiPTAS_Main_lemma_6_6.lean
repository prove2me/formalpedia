-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_lemma_6_6
-- name    : MinSumRadiiPTAS.Main.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:07:00.642505+00:00
-- url     : https://prove2.me/theorems/7e889d41-ef25-4149-ae2d-8bbc76072a16
-- title:
--   Lemma 6.6 — few significant net points near $p$: at most $18(\rho + 4a_i + \lambda)/(a_{i-1} + \lambda)$
-- statement:
--   **Lemma 6.6** (p. 27). In Case II on a normalised instance, after any terminated run of the preprocessing (leaving $P''$), for any optimal $O_{3R}$ for $P''$, any shift $\sigma \in \{0, \dots, L-1\}$ ($L = \lceil e^{7100}/\varepsilon\rceil$, thresholds $a_i$ with target $3R$), any level $1 \le i \le t$, any $6a_i$-net $N_i$ of $Z_i$ and any choice of certified balls $C_s \in \mathcal C_R$ with $s \in C_s$ and $r_{C_s} \in (a_{i-1}, a_i]$ for $s \in N_i$: for every $p \in P$ and $\rho \ge 0$ with $\rho + 4a_i \le r_{\max} - 2R$, the number of significant net points of $N_i$ (w.r.t. $O_{3R}$ and the chosen $C_s$) at distance $\le \rho$ from $p$ is at most
--   $$\frac{18(\rho + 4a_i + \lambda)}{a_{i-1} + \lambda}.$$
--
--   Differences from the source:
--   - encoding: point set P with |P| = n, a metric d on P → points Fin n (0-based), d : Fin n → Fin n → ℝ with the published MinSumClust.IsMetric (d(p,p)=0, d ≥ 0, symmetry, triangle inequality, d(p,q) > 0 for p ≠ q); reason: same instances
--   - reading: the lemma's own sentence (context of §6) → explicit hypotheses: StandingInstance d k ε (Lemma 2.1's normalisation: integer distances in [1, ⌈10k/ε⌉], opt ≤ 8k/ε, 1 ≤ k ≤ n), ε ∈ (0, 1/10), λ ∈ [ε/k, 10k/ε] (Theorem 6.1); reason: p. 7 assumes the normalisation for the rest of the paper, p. 6 fixes ε ∈ (0, 1/10), and §6 works under Theorem 6.1's λ; trap 19 (section standing assumptions are binders)
--   - reading: P″ and O_{3R} of §6.2 (Case II, λ < 6R) → P″ := preFinal of any terminated run of the preprocessing (IsPreprocessingRun) from any client set P′, O_{3R} any optimal cover of P″ by balls of 𝔅 of radius ≤ 3R (IsOptCover); reason: the paper's preprocessing picks dense balls in an arbitrary order and O_{3R} is any optimal solution; the statement holds for all of them
--   - reading: N_i = Net(Z_i, 6a_i), C_s "an arbitrary certified ball that contains s", a fixed σ → every σ < L, every 6a_i-net N of Z_i, every choice function Cs with the stated properties; reason: the paper's choices are arbitrary; the statement holds for all of them
--   - generalization: p. 26 assumes R ≤ ⌈10k/ε⌉ without loss before the bounded-radius DP analysis → no upper bound on R beyond the Case II condition λ < 6R; reason: this includes every source instance. Above the maximum distance all minimal balls are allowed and no dense preprocessing ball exists; extra threshold levels have empty nets and only a far child. The algorithm can cap R and use Case I if needed
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §6.2, Lemma 6.6, p. 27

import Mathlib
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumRadiiPTAS_Main_LP
import Definitions.Def_MinSumRadiiPTAS_Main_Partition
import Definitions.Def_MinSumRadiiPTAS_Main_CaseII

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-- **Lemma 6.6** (p. 27): in Case II on a normalised instance, after any terminated run of the
preprocessing (client set `P″`), for any optimal `O_{3R}` for `P″`, any shift `σ ∈ {0, …, L−1}`
(`L = ⌈e^{7100}/ε⌉`, thresholds `a_i = thr λ L σ i` with target `3R`), any level `1 ≤ i ≤ t`, any
`6a_i`-net `N_i` of `Z_i` and any choice of certified balls `C_s ∈ C_R` with `s ∈ C_s` and
`r_{C_s} ∈ (a_{i−1}, a_i]`: for every `p ∈ P` and `ρ ≥ 0` with `ρ + 4a_i ≤ r_max − 2R`, the number of
significant net points of `N_i` at distance `≤ ρ` from `p` is at most
`18(ρ + 4a_i + λ)/(a_{i−1} + λ)`. -/
theorem lemma_6_6 {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε lam R : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1 / 10) (hI : StandingInstance d k ε) (hlam1 : ε / k ≤ lam)
    (hlam2 : lam ≤ 10 * k / ε) (hcase : lam < 6 * R) (P1 : Finset (Fin n))
    (steps : List (Fin n × ℝ)) (hrun : IsPreprocessingRun d lam ε R P1 steps)
    (O3 : Finset (Ball n))
    (hO3 : IsOptCover d lam (fun B => B.radius ≤ 3 * R) (preFinal d R P1 steps) O3)
    (σ : ℕ) (hσ : σ < L6 ε) (i : ℕ) (hi1 : 1 ≤ i) (hit : i ≤ thrTop lam (3 * R) (L6 ε) σ)
    (N : Finset (Fin n))
    (hN : IsNet d (zoneR d lam R (preFinal d R P1 steps) (thr lam (L6 ε) σ (i - 1))
      (thr lam (L6 ε) σ i)) N (6 * thr lam (L6 ε) σ i))
    (Cs : Fin n → Ball n)
    (hCs : ∀ s ∈ N, IsCertifiedR d lam R (preFinal d R P1 steps) (Cs s) ∧ s ∈ (Cs s).pts d ∧
      thr lam (L6 ε) σ (i - 1) < (Cs s).radius ∧ (Cs s).radius ≤ thr lam (L6 ε) σ i)
    (p : Fin n) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ + 4 * thr lam (L6 ε) σ i ≤ rmax ε R - 2 * R) :
    ((N.filter (fun s => IsSignificant d O3 (thr lam (L6 ε) σ i) (Cs s) ∧ d p s ≤ ρ)).card : ℝ) ≤
      18 * (ρ + 4 * thr lam (L6 ε) σ i + lam) / (thr lam (L6 ε) σ (i - 1) + lam) := by sorry

end MinSumRadiiPTAS.Main
