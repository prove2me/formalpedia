-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_archRealLift3_mul_of_archComponent3_eq_one
-- name    : LanglandsTunnell.CubicInduction.exists_eq_archRealLift3_mul_of_archComponent3_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/44d4d804-4774-5d1f-bc6d-45e39879401a
-- title:
--   Archimedean splitting of GL₃ of the adeles of ℚ
-- statement:
--   Let $k_0$ be an element of `AdelicGL 3 (𝓞 ℚ) ℚ`, that is, of the general linear group $GL_3$ over the adele ring $\mathbb{A}_{\mathbb{Q}}$ of $\mathbb{Q}$ (formed from $\mathbb{Z} = \mathcal{O}_{\mathbb{Q}}$ and $\mathbb{Q}$). The assertion is that there exist a family of real numbers $c : \mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}$ and an element $k_1$ of $GL_3(\mathbb{A}_{\mathbb{Q}})$ such that three conditions hold simultaneously: first, the $3 \times 3$ real matrix with entries $c$ has nonzero determinant; second, the archimedean component of $k_1$ is the identity, where `archComponent3` is the group homomorphism $GL_3(\mathbb{A}_{\mathbb{Q}}) \to GL_3(\mathbb{A}_{\mathbb{Q},\infty})$ obtained by applying the projection `AdelicLevel.adeleArch` from the adeles to the infinite adeles entrywise; and third, $k_0 = \mathrm{archRealLift3}(c) \cdot k_1$ in $GL_3(\mathbb{A}_{\mathbb{Q}})$. Here `archRealLift3` sends a real matrix $c$ to the adelic matrix obtained by applying [`AutomorphicForm.StandardKernel.ofReal`](def/AutomorphicForm_SmoothingKernel.html#L774) to each entry and then the archimedean inclusion [`AutomorphicForm.archMatrixInclN`](def/AutomorphicForm_SmoothingKernel.html#L95) into matrices over $\mathbb{A}_{\mathbb{Q}}$, and returns the associated element of $GL_3(\mathbb{A}_{\mathbb{Q}})$ when that matrix is a unit, and the identity otherwise.
--
--   This is the elementary splitting of $GL_3(\mathbb{A}_{\mathbb{Q}})$ into a real matrix placed at the infinite place times an element with trivial archimedean component, used to normalise the archimedean part of a point in the adelic group. It is invoked in the construction of the induced-picture package attached to a top double-slot coefficient, `exists_submodule_inducedPicture_package_of_doubleSlotCoeff_top`, where a point of non-vanishing of an equivariant function is moved to one with trivial archimedean part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_eq_archRealLift3_mul_of_archComponent3_eq_one.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_eq_archRealLift3_mul_of_archComponent3_eq_one
    (k₀ : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∃ (c : Fin 3 → Fin 3 → ℝ) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ), (Matrix.of c).det ≠ 0 ∧ archComponent3 (𝓞 ℚ) ℚ k₁ = 1 ∧
      k₀ = WhittakerBlock.archRealLift3 c * k₁ := by sorry
