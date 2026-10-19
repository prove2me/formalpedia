-- Prove2me | Theorems.Thm_OAI_PettyProjection_FixedPoint_no_C1_retraction_closedBall
-- name    : OAI.PettyProjection.FixedPoint.no_C1_retraction_closedBall
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:05:56.573812+00:00
-- url     : https://prove2.me/theorems/254bffda-6a85-44ac-8701-7782e2aff9c0
-- title:
--   No C¹ retraction of the closed unit ball onto the unit sphere in a finite-dimensional real inner product space
-- statement:
--   Let $E$ be a finite-dimensional real inner product space (`NormedAddCommGroup E`, `InnerProductSpace ℝ E`, `FiniteDimensional ℝ E`; $E$ may live in any universe), and let $B = \{x : \|x\| \le 1\}$ be its closed unit ball (`closedBall (0:E) 1`). Let $r : E \to E$ be a function and $r' : E \to (E \to_L E)$ an assignment of continuous linear maps $E \to E$. Suppose that:
--   - for every $x \in B$, $r$ has derivative $r'(x)$ at $x$ within $B$ (`HasFDerivWithinAt r (r' x) (closedBall (0:E) 1) x`);
--   - $r'$ is continuous on $B$ (`ContinuousOn r' (closedBall (0:E) 1)`), for the operator-norm topology;
--   - $\|r(x)\| = 1$ for every $x \in B$;
--   - $r(x) = x$ for every $x \in E$ with $\|x\| = 1$.
--
--   Then these hypotheses are contradictory: the conclusion is `False`. In other words, there is no retraction of $B$ onto its unit sphere that is $C^1$ on $B$ in this sense.
--
--   Only the behaviour of $r$ on $B$ matters. Nothing is assumed about $r$ or $r'$ outside $B$. If $E = \{0\}$ the sphere is empty, and the hypothesis $\|r(0)\| = 1$ alone is already impossible.
--
--   Lean: `OAI.PettyProjection.FixedPoint.no_C1_retraction_closedBall`. OpenAI's lemma `no_smooth_retraction` states the same with an extra argument: a Borel measurable structure on $E$ and an additive Haar measure $\mu$ on it. This statement drops that argument, since such a measure always exists. Its proof chooses one (`borelize E`, `Measure.addHaar`) and applies OpenAI's lemma. The statement uses only Mathlib.
-- source:
--   J. Milnor, Analytic proofs of the "hairy ball theorem" and the Brouwer fixed point theorem, American Mathematical Monthly 85 (1978), 521–524; C. A. Rogers, A less strange version of Milnor's proof of Brouwer's fixed-point theorem, American Mathematical Monthly 87 (1980), 525–527 (the determinant-polynomial method). Proof: OpenAI, Petty's projection-volume conjecture in dimensions at least four, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 088, commit adc7f12, Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/ProjectionBodies/FixedPointCalculus.lean (OpenAI's lemma OAI.PettyProjection.FixedPoint.no_smooth_retraction, restated without its measure argument)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX uι uα

noncomputable section
open Set Metric MeasureTheory
namespace PettyProjection.FixedPoint

theorem no_C1_retraction_closedBall {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {r : E → E} {r' : E → E →L[ℝ] E}
    (hd : ∀ x ∈ closedBall (0:E) 1, HasFDerivWithinAt r (r' x) (closedBall (0:E) 1) x)
    (hc : ContinuousOn r' (closedBall (0:E) 1))
    (hnorm : ∀ x ∈ closedBall (0:E) 1, ‖r x‖ = 1)
    (hb : ∀ x : E, ‖x‖ = 1 → r x = x) : False := by
  sorry

end PettyProjection.FixedPoint
end

end OAI
end
