-- Prove2me | Theorems.Thm_Maldacena1999_conformal_ode_solution
-- name    : Maldacena1999.conformal_ode_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T17:50:50.645668+00:00
-- url     : https://prove2.me/theorems/9389d917-bee5-404d-bc1c-28be9e3c625e
-- title:
--   Solutions of the conformal-invariance ODE (2.9): $f=b\sqrt{1+\tilde R^4 z}-c$
-- statement:
--   Let $\tilde R>0$, $c\in\mathbb R$, and let $f$ be differentiable on the interval $I=(-1/\tilde R^4,\infty)$. Then $f$ satisfies the equation (2.9)
--   $$f(z)+c=2\Big(z+\frac{1}{\tilde R^4}\Big)f'(z)\qquad\text{for all }z\in I$$
--   if and only if there is a constant $b\in\mathbb R$ with
--   $$f(z)=b\sqrt{1+\tilde R^4z}-c\qquad\text{for all }z\in I .$$
--
--   In the paper this equation expresses invariance of the probe action (2.7) under the special conformal transformations (2.8); its solution $f=b[\sqrt{1+\tilde R^4z}-a]$ (the case $c=ab$) is the Born-Infeld form that, after fixing the constants, reproduces the D3-brane probe action (2.6) with $\tilde R^4=4\pi gN$.
--
--   **Formalization Note** The paper only states that the given $f$ solves (2.9); the milestone is stated as a characterisation of all differentiable solutions on the natural domain $1+\tilde R^4z>0$. The constant solution $f\equiv-c$ corresponds to $b=0$ and is not of the paper's form $b[\sqrt{\cdot}-a]$ unless $c=0$, which is why the constant is written as $-c$ rather than $-ab$.
-- source:
--   J. Maldacena, The Large-N Limit of Superconformal Field Theories and Supergravity, Int. J. Theor. Phys. 38 (1999) 1113-1133, https://doi.org/10.1023/A:1026654312961 (arXiv:hep-th/9711200), Section 2, eq. (2.9) and the sentence after it, p. 1119

import Mathlib
import Definitions.Def_Maldacena1999_Defs

open Filter Topology

namespace Maldacena1999

theorem conformal_ode_solution (Rt : ℝ) (hRt : 0 < Rt) (c : ℝ) (f : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioi (-1 / Rt ^ 4))) :
    (∀ z ∈ Set.Ioi (-1 / Rt ^ 4), f z + c = 2 * (z + 1 / Rt ^ 4) * deriv f z) ↔
      ∃ b : ℝ, ∀ z ∈ Set.Ioi (-1 / Rt ^ 4), f z = b * Real.sqrt (1 + Rt ^ 4 * z) - c := by
  sorry

end Maldacena1999
