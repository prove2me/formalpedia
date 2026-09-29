-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_archRealLift3_one_and_ideleNorm_det_archRealLift3
-- name    : LanglandsTunnell.CubicInduction.WhittakerBlock.archRealLift3_one_and_ideleNorm_det_archRealLift3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/cedec64a-7672-5d98-8659-e997e7ba30a6
-- title:
--   Archimedean real lift: identity at 1, idele norm of determinant
-- statement:
--   Work over $\mathbb{Q}$, with $\mathbb{A}_{\mathbb{Q}} =$ `AdeleRing (𝓞 ℚ) ℚ` and `AdelicGL 3 (𝓞 ℚ) ℚ` the general linear group $GL_3(\mathbb{A}_{\mathbb{Q}})$. For a real array $e : \mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}$, [`WhittakerBlock.archRealMat3 e`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L13) is the adelic $3\times 3$ matrix obtained by applying [`AutomorphicForm.archMatrixInclN`](def/AutomorphicForm_SmoothingKernel.html#L95) to the matrix of entries `StandardKernel.ofReal (e i j)`, i.e. the matrix placed at the archimedean components and the identity at the finite part, and [`WhittakerBlock.archRealLift3 e`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18) is the corresponding element of $GL_3(\mathbb{A}_{\mathbb{Q}})$ when that matrix is a unit and $1$ otherwise. The theorem asserts two things. First, for the Kronecker array $e(a,b) = 1$ if $a = b$ and $0$ otherwise, `archRealLift3 e` is the identity of $GL_3(\mathbb{A}_{\mathbb{Q}})$. Second, for every $e$ with $\det(\mathrm{of}\,e) > 0$, the real number [`NumberField.TateGlobal.ideleNorm ℚ`](def/NumberField_TateGlobalZeta.html#L19) of the determinant of `archRealLift3 e` — that is, the value at that idele of the distributive Haar character of $\mathbb{A}_{\mathbb{Q}}$, read as a real number — equals $\det(\mathrm{of}\,e)$.
--
--   This records the normalisation of the idelic modulus on the archimedean lift of a real matrix: the determinant idele of such a lift has trivial finite part and archimedean part $\det e$, so its idele norm is $|\det e|$. It is used in the archimedean one-parameter flows on $GL_3(\mathbb{A}_{\mathbb{Q}})$, where the determinant slab of the idele norm has to be tracked, and is cited by the differentiability statements for the smoothing operator and the archimedean derivative along `archRealLift3`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_archRealLift3_one_and_ideleNorm_det_archRealLift3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.WhittakerBlock.archRealLift3_one_and_ideleNorm_det_archRealLift3 :
    WhittakerBlock.archRealLift3 (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0) = 1 ∧
    ∀ e : Fin 3 → Fin 3 → ℝ, 0 < (Matrix.of e).det →
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (WhittakerBlock.archRealLift3 e)) =
        (Matrix.of e).det := by sorry
