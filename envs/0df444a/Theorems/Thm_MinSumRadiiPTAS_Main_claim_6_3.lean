-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_claim_6_3
-- name    : MinSumRadiiPTAS.Main.claim_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:06:19.572281+00:00
-- url     : https://prove2.me/theorems/a113bbc2-c53a-437e-9e5d-2b80f99a06c7
-- title:
--   Claim 6.3 — preprocessing: $\mathrm{cost}_\lambda(S) + \mathrm{cost}_\lambda(O_{3R}) \le \mathrm{cost}_\lambda(O_R)$
-- statement:
--   **Claim 6.3** (p. 25). Let $\varepsilon \in (0, 1/10)$, $(n, k, d)$ a normalised instance, $\lambda \in [\varepsilon/k, 10k/\varepsilon]$ and $\lambda < 6R$ (Case II). Let $S$ be the balls of any terminated run of the preprocessing from a client set $P'$ and $P''$ the client set it leaves, $O_R$ any optimal cover of $P'$ by balls of $\mathfrak B$ of radius $\le R$, and $O_{3R}$ any optimal cover of $P''$ by balls of $\mathfrak B$ of radius $\le 3R$. Then
--   $$\mathrm{cost}_\lambda(S) + \mathrm{cost}_\lambda(O_{3R}) \le \mathrm{cost}_\lambda(O_R).$$
--
--   Differences from the source:
--   - encoding: point set P with |P| = n, a metric d on P → points Fin n (0-based), d : Fin n → Fin n → ℝ with the published MinSumClust.IsMetric (d(p,p)=0, d ≥ 0, symmetry, triangle inequality, d(p,q) > 0 for p ≠ q); reason: same instances
--   - reading: the lemma's own sentence (context of §6) → explicit hypotheses: StandingInstance d k ε (Lemma 2.1's normalisation: integer distances in [1, ⌈10k/ε⌉], opt ≤ 8k/ε, 1 ≤ k ≤ n), ε ∈ (0, 1/10), λ ∈ [ε/k, 10k/ε] (Theorem 6.1); reason: p. 7 assumes the normalisation for the rest of the paper, p. 6 fixes ε ∈ (0, 1/10), and §6 works under Theorem 6.1's λ; trap 19 (section standing assumptions are binders)
--   - reading: P″ and O_{3R} of §6.2 (Case II, λ < 6R) → P″ := preFinal of any terminated run of the preprocessing (IsPreprocessingRun) from any client set P′, O_{3R} any optimal cover of P″ by balls of 𝔅 of radius ≤ 3R (IsOptCover); reason: the paper's preprocessing picks dense balls in an arbitrary order and O_{3R} is any optimal solution; the statement holds for all of them
--   - encoding: the set S of balls of the preprocessing → the list preBalls R steps, cost_λ counting every entry; reason: a pick removes the points of its ball, so no ball is picked twice
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §6.2, Claim 6.3, p. 25

import Mathlib
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumRadiiPTAS_Main_LP
import Definitions.Def_MinSumRadiiPTAS_Main_CaseII

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-- **Claim 6.3** (p. 25): in Case II (`λ ∈ [ε/k, 10k/ε]`, `λ < 6R`) on a normalised instance, let
`S` be the balls of any terminated run of the preprocessing from `P′`, `P″` the client set it
leaves, `O_R` an optimal cover of `P′` by balls of `𝔅` of radius `≤ R` and `O_{3R}` an optimal cover
of `P″` by balls of `𝔅` of radius `≤ 3R`. Then `cost_λ(S) + cost_λ(O_{3R}) ≤ cost_λ(O_R)`. -/
theorem claim_6_3 {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε lam R : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1 / 10) (hI : StandingInstance d k ε) (hlam1 : ε / k ≤ lam)
    (hlam2 : lam ≤ 10 * k / ε) (hcase : lam < 6 * R) (P1 : Finset (Fin n))
    (steps : List (Fin n × ℝ)) (hrun : IsPreprocessingRun d lam ε R P1 steps)
    (OR : Finset (Ball n)) (hOR : IsOptCover d lam (fun B => B.radius ≤ R) P1 OR)
    (O3 : Finset (Ball n))
    (hO3 : IsOptCover d lam (fun B => B.radius ≤ 3 * R) (preFinal d R P1 steps) O3) :
    lcostL lam (preBalls R steps) + costL lam O3 ≤ costL lam OR := by sorry

end MinSumRadiiPTAS.Main
