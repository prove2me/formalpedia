-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_lemma_6_4
-- name    : MinSumRadiiPTAS.Main.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:06:11.682948+00:00
-- url     : https://prove2.me/theorems/d7405f5a-2035-4f54-9c3a-66e036da8234
-- title:
--   Lemma 6.4 — local sparsity: the balls of $O_{3R}$ inside $\mathrm{Ball}(p,\rho)$ cost $\le 6(\rho+\lambda)$
-- statement:
--   **Lemma 6.4** (local sparsity, p. 25). In Case II on a normalised instance ($\varepsilon \in (0, 1/10)$, $\lambda \in [\varepsilon/k, 10k/\varepsilon]$, $\lambda < 6R$), after any terminated run of the preprocessing (leaving $P''$) and for any optimal $O_{3R}$ for $P''$: for every $p \in P$ and every $0 \le \rho \le r_{\max} - 2R$, the balls of $O_{3R}$ whose point sets are contained in $\mathrm{Ball}(p, \rho)$ have total cost
--   $$\mathrm{cost}_\lambda\big(\{B \in O_{3R} : B \subseteq \mathrm{Ball}(p,\rho)\}\big) \le 6(\rho + \lambda).$$
--
--   Differences from the source:
--   - encoding: point set P with |P| = n, a metric d on P → points Fin n (0-based), d : Fin n → Fin n → ℝ with the published MinSumClust.IsMetric (d(p,p)=0, d ≥ 0, symmetry, triangle inequality, d(p,q) > 0 for p ≠ q); reason: same instances
--   - reading: the lemma's own sentence (context of §6) → explicit hypotheses: StandingInstance d k ε (Lemma 2.1's normalisation: integer distances in [1, ⌈10k/ε⌉], opt ≤ 8k/ε, 1 ≤ k ≤ n), ε ∈ (0, 1/10), λ ∈ [ε/k, 10k/ε] (Theorem 6.1); reason: p. 7 assumes the normalisation for the rest of the paper, p. 6 fixes ε ∈ (0, 1/10), and §6 works under Theorem 6.1's λ; trap 19 (section standing assumptions are binders)
--   - reading: P″ and O_{3R} of §6.2 (Case II, λ < 6R) → P″ := preFinal of any terminated run of the preprocessing (IsPreprocessingRun) from any client set P′, O_{3R} any optimal cover of P″ by balls of 𝔅 of radius ≤ 3R (IsOptCover); reason: the paper's preprocessing picks dense balls in an arbitrary order and O_{3R} is any optimal solution; the statement holds for all of them
--   - encoding: ρ ≤ r_max − 2R (the radius of Ball(p, ρ)) → 0 ≤ ρ ≤ r_max − 2R; reason: radii are nonnegative (p. 1); for ρ < −λ the printed bound would be negative, a case the paper never considers
--   - encoding: "the total cost of the balls of O_{3R} contained inside Ball(p, ρ)" → cost_λ of the balls of O_{3R} whose point sets (in P) are subsets of that of Ball(p, ρ); reason: the proof bounds cost_λ(W) for exactly this W; containment of balls is containment of point sets of P
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §6.2, Lemma 6.4, p. 25 (proof p. 26)

import Mathlib
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumRadiiPTAS_Main_LP
import Definitions.Def_MinSumRadiiPTAS_Main_CaseII

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-- **Lemma 6.4** (local sparsity, p. 25): in Case II on a normalised instance, after any terminated
run of the preprocessing (client set `P″`) and for any optimal `O_{3R}` for `P″`: for every
`p ∈ P` and every radius `0 ≤ ρ ≤ r_max − 2R`, the balls of `O_{3R}` contained in `Ball(p, ρ)`
have total cost `cost_λ ≤ 6(ρ + λ)`. -/
theorem lemma_6_4 {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε lam R : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1 / 10) (hI : StandingInstance d k ε) (hlam1 : ε / k ≤ lam)
    (hlam2 : lam ≤ 10 * k / ε) (hcase : lam < 6 * R) (P1 : Finset (Fin n))
    (steps : List (Fin n × ℝ)) (hrun : IsPreprocessingRun d lam ε R P1 steps)
    (O3 : Finset (Ball n))
    (hO3 : IsOptCover d lam (fun B => B.radius ≤ 3 * R) (preFinal d R P1 steps) O3)
    (p : Fin n) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ rmax ε R - 2 * R) :
    costL lam (O3.filter (fun B => B.pts d ⊆ Ball.pts d ⟨p, ρ⟩)) ≤ 6 * (ρ + lam) := by sorry

end MinSumRadiiPTAS.Main
