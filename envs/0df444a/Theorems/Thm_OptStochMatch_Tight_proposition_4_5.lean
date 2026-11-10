-- Prove2me | Theorems.Thm_OptStochMatch_Tight_proposition_4_5
-- name    : OptStochMatch.Tight.proposition_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:57:59.056263+00:00
-- url     : https://prove2.me/theorems/36dfbb3f-9ed1-4026-b1de-8406f569c988
-- title:
--   Proposition 4.5 — coordinatewise guarantee of the posterior allocation policy
-- statement:
--   For every compact, convex, downward-closed $P\subseteq\mathbb R^m_+$ containing $0$ and every measurable offline allocation $Y$ ($Y(z)\in P$, $0\le Y(z)\le z$), the posterior allocation policy (4.1) exists and, under it, every job satisfies $\mathbb E[x_i(1)]\ge(1-e^{1-e})\,\mathbb E[Y_i(Z)]$.
--
--   Differences from the source:
--   - encoding: the posterior allocation policy (4.1) → any SchedPolicy whose rate equals (4.1) after every completion history with nonnegative accumulated work (FollowsPosterior); reason: this gives a feedback-rule extension to all nonnegative states, including every reachable state; negative-work states are irrelevant to the source process
--   - encoding: expectations of nonnegative quantities → lower Lebesgue integrals in ℝ≥0∞; reason: the integrands are nonnegative, so the values agree; no integrability side condition can be vacuous
--   - reading: the policy (4.1) constructed from Y (§4.1) → existence of a policy following (4.1) is part of the conclusion, and the bound holds for every such policy; reason: the source constructs the policy before stating the bound; asserting its existence keeps the statement from being vacuous
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Proposition 4.5, p. 17 (PDF p. 18), with the construction of §4.1, pp. 13–14 (PDF pp. 14–15)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Laws
import Definitions.Def_OptStochMatch_Tight_Scheduling
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace OptStochMatch.Tight

/-- Proposition 4.5 (p. 17, PDF 18), with the construction of §4.1 (p. 13, PDF 14). For every
compact, convex, downward-closed feasible-rate region `P ⊆ ℝ^m_+` containing `0` and every
measurable offline allocation `Y` (`Y(z) ∈ P`, `0 ≤ Y(z) ≤ z`), the posterior allocation policy
(4.1) exists, and every job `i` satisfies `E[x_i(1)] ≥ (1 − e^{1−e}) E[Y_i(Z)]` under it. -/
theorem proposition_4_5 {m : ℕ} (P : Set (Fin m → ℝ)) (hP : IsRateRegion P)
    (Y : (Fin m → ℝ) → (Fin m → ℝ)) (hY : IsOfflineAllocation P Y) :
    (∃ σ : SchedPolicy m P, FollowsPosterior Y σ) ∧
    ∀ σ : SchedPolicy m P, FollowsPosterior Y σ → ∀ i : Fin m,
      ENNReal.ofReal cStar * ∫⁻ z, ENNReal.ofReal (Y z i) ∂(demandLaw m) ≤ expWorkJob σ i := by sorry

end OptStochMatch.Tight
