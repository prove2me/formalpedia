-- Prove2me | Theorems.Thm_LesHouchesWidth_jacobianEntry_law_indep_input
-- name    : LesHouchesWidth.jacobianEntry_law_indep_input
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T22:19:43.629667+00:00
-- url     : https://prove2.me/theorems/cc50696d-d366-4b4a-be86-1c281a0eb7c1
-- title:
--   Section 5.4: the law of the Jacobian entry does not depend on the input
-- statement:
--   Under the standing assumptions of Section 5.3, for all nonzero inputs $x,x'\in\mathbb R^{n_0}$ and all $p,q$, the random variables
--   $$\frac{\partial z^{(L+1)}_q}{\partial x_p}(x)\qquad\text{and}\qquad\frac{\partial z^{(L+1)}_q}{\partial x_p}(x')$$
--   have the same distribution.
--
--   This allows the moment computations of Section 5.5 to be carried out at any convenient nonzero input.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 40, Section 5.4, first exercise ("Conclude that the distribution of $\partial z_p/\partial x_q$ is the same for all $x\neq 0$").

import Mathlib
import Definitions.Def_LesHouchesWidth_ReLUNet

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem jacobianEntry_law_indep_input (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ_ac : μ ≪ volume) (hμ_symm : μ.map (fun t : ℝ => -t) = μ)
    (hμ_var : ∫ t, t ^ 2 ∂μ = 1)
    (L : ℕ) (hL : 1 ≤ L) (n : ℕ → ℕ) (hn : ∀ ℓ ≤ L + 1, 1 ≤ n ℓ)
    (x x' : Fin (n 0) → ℝ) (hx : x ≠ 0) (hx' : x' ≠ 0)
    (p : Fin (n 0)) (q : Fin (n (L + 1))) :
    (weightLaw n L μ).map (fun ω => jacobianEntry ω x p q) =
      (weightLaw n L μ).map (fun ω => jacobianEntry ω x' p q) := by sorry

end LesHouchesWidth
