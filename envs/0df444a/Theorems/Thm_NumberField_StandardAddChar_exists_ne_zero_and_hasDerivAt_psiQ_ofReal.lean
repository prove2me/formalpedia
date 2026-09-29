-- Prove2me | Theorems.Thm_NumberField_StandardAddChar_exists_ne_zero_and_hasDerivAt_psiQ_ofReal
-- name    : NumberField.StandardAddChar.exists_ne_zero_and_hasDerivAt_psiQ_ofReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/be441176-207a-5050-9448-604637aa41e0
-- title:
--   Non-vanishing derivative at 0 of s↦ψ_ℚ(ι(s),0)
-- statement:
--   The assertion is an unconditional existence statement about the standard additive character of the adeles of $\mathbb{Q}$, with no parameters or hypotheses. Here `psiQ` is the additive character of `AdeleRing (𝓞 ℚ) ℚ` whose value at an adele $x$ is the product $\mathrm{psiArch}(x_1)\cdot\mathrm{psiFin}(x_2)$ of its archimedean and finite components, where $\mathrm{psiArch}$ is the finitary product over the infinite places $v$ of $\mathbb{Q}$ of the local characters $\mathrm{psiArchPlace}\,v$ evaluated at the coordinates $x_1(v)$, and $\mathrm{psiFin}$ is the finitary product over the height-one primes $v$ of $\mathcal{O}_{\mathbb{Q}}$ of the local characters $\mathrm{psiV}\,v$ evaluated at $x_2(v)$. For a real number $s$, `ofReal s` denotes the infinite adele of $\mathbb{Q}$ whose coordinate at each infinite place $v$ is the image of $s$ under the inverse of the ring isomorphism between the completion of $\mathbb{Q}$ at $v$ and $\mathbb{R}$ coming from $v$ being real. The theorem states that there exists a complex number $\lambda \neq 0$ such that the function $\mathbb{R}\to\mathbb{C}$, $s \mapsto$ `psiQ` applied to the adele with archimedean part `ofReal s` and zero finite part, is differentiable at $0$ with derivative $\lambda$ there. Only non-vanishing of the derivative is claimed, not its value.
--
--   This is the infinitesimal form of the non-triviality of the archimedean component of the standard additive character $\psi$ of $\mathbb{A}_{\mathbb{Q}}$, restricted to the one-parameter real line at the unique infinite place. It is used in the construction of Whittaker functionals, where one differentiates along a one-parameter unipotent subgroup and needs the resulting constant to be invertible; it feeds [`LanglandsTunnell.CubicInduction.exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv`](thm.html#LanglandsTunnell.CubicInduction.exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_StandardAddChar_exists_ne_zero_and_hasDerivAt_psiQ_ofReal.lean

import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem
NumberField.StandardAddChar.exists_ne_zero_and_hasDerivAt_psiQ_ofReal :
    ∃ lam : ℂ, lam ≠ 0 ∧
      HasDerivAt
        (fun s : ℝ => NumberField.StandardAddChar.psiQ
          ((AutomorphicForm.StandardKernel.ofReal s, 0) : AdeleRing (𝓞 ℚ) ℚ))
        lam 0 := by sorry
