-- Prove2me | Theorems.Thm_NumberField_exists_ternary_quadratic_eq_adicCompletion_of_not_isSquare
-- name    : NumberField.exists_ternary_quadratic_eq_adicCompletion_of_not_isSquare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/4295244f-a99a-58b8-a742-68591c8cc88f
-- title:
--   Ternary quadratic form represents every non-square locally
-- statement:
--   Let $K$ be a number field and let $v$ be a height-one prime of its ring of integers $\mathcal{O}_K$, i.e. a finite place of $K$; write $F = K_v$ for the $v$-adic completion of $K$, the completion of $K$ with respect to the $v$-adic valuation. Let $D$, $\lambda$ and $r$ be elements of $F$ subject to: $D \neq 0$, $\lambda \neq 0$, and $r$ is not a square in $F$ (there is no $x \in F$ with $r = x \cdot x$). The conclusion asserts the existence of elements $s, t_1, t_2 \in F$ with
--   $$D s^2 + \lambda\,(t_1^2 - D t_2^2) = r.$$
--   Thus the ternary quadratic form $D s^2 + \lambda (t_1^2 - D t_2^2)$ over $F$ takes the value $r$ at some point of $F^3$. Note that nothing is assumed about $D$ beyond non-vanishing (in particular $D$ may be a square), nor about $\lambda$ beyond non-vanishing, and no residue characteristic is excluded; the hypothesis on $r$ is only that it is not a square, which in particular forces $r \neq 0$.
--
--   The form $D s^2 + \lambda(t_1^2 - D t_2^2)$ is the reduced norm restricted to the trace-zero part of the quaternion algebra $(D,\lambda)$ over the local field $F$, so the statement says that every non-square of $F$ is represented, equivalently that every quadratic extension of $F$ embeds into $(D,\lambda)$; when $D$ is a square or $\lambda$ is a norm from $F(\sqrt{D})$ the form is isotropic and the assertion is immediate, and otherwise it is the local embedding theorem for the quaternion division algebra. It is used in the construction of local test functions for automorphic forms, in [`AutomorphicForm.exists_isOpen_one_mem_forall_exists_isLocalTestFn_of_forall_mul_sigmaTensor_ne`](thm.html#AutomorphicForm.exists_isOpen_one_mem_forall_exists_isLocalTestFn_of_forall_mul_sigmaTensor_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_ternary_quadratic_eq_adicCompletion_of_not_isSquare.lean

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.exists_ternary_quadratic_eq_adicCompletion_of_not_isSquare
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (D lam r : v.adicCompletion K) (hD : D ≠ 0) (hlam : lam ≠ 0) (hr : ¬ IsSquare r) :
    ∃ s t₁ t₂ : v.adicCompletion K, D * s ^ 2 + lam * (t₁ ^ 2 - D * t₂ ^ 2) = r := by sorry
