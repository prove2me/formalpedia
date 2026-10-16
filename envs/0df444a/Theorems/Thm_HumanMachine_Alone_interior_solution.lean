-- Prove2me | Theorems.Thm_HumanMachine_Alone_interior_solution
-- name    : HumanMachine.Alone.interior_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:29:14.836583+00:00
-- url     : https://prove2.me/theorems/45f11a84-605c-4f26-ad0d-567f65f2e1d5
-- title:
--   Appendix A — interior solution of the choice equation
-- statement:
--   Let $\lambda>0$, $0<\mu<1$, and $0<p<1$. If $p$ satisfies the equation obtained by substituting Lemma 1's conditional choice probabilities into $p=(1-\mu)p_b+\mu p_g$, then
--
--   $$
--   p=\bar p:=\frac{\mu}{1-e^{-1/\lambda}}-\frac{1-\mu}{e^{1/\lambda}-1}.
--   $$
--
--   This identifies the only possible interior value before the boundary cases are considered.
--
--   **Formalization Note** The equation and the interior condition are explicit hypotheses; the result does not claim that the algebraic candidate is feasible or optimal for every prior.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), p. 32 (PDF p. 33), proof of Theorem 1, first two displays.

import Mathlib
import Definitions.Def_HumanMachine_Alone_model

namespace HumanMachine.Alone

theorem interior_solution (lam mu p : ℝ) (hlam : 0 < lam)
    (hmu0 : 0 < mu) (hmu1 : mu < 1) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (heq : p = (1 - mu) * (p / (p + (1 - p) * Real.exp (1 / lam))) +
      mu * (p * Real.exp (1 / lam) / (p * Real.exp (1 / lam) + 1 - p))) :
    p = pBar lam mu := by sorry

end HumanMachine.Alone
