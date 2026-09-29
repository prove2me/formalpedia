-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_componentAt3_archRealLift3_eq_one_and_realMat_archComponent3_eq
-- name    : LanglandsTunnell.CubicInduction.componentAt3_archRealLift3_eq_one_and_realMat_archComponent3_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/93cef746-4408-5116-9fa5-a8a201a86a7f
-- title:
--   Archimedean real lift in GL₃(A_ℚ): components and orthogonality
-- statement:
--   Let $e : \mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}$ be a real $3\times 3$ array whose associated matrix `Matrix.of e` has nonzero determinant, and let [`WhittakerBlock.archRealLift3 e`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18) be the element of $GL_3(\mathbb{A}_\mathbb{Q})$ obtained from the adelic matrix whose entries are the images of the $e_{ij}$ under the inclusion of $\mathbb{R}$ into the infinite adeles, placed in the archimedean factor by `archMatrixInclN` (the construction takes this matrix's unit when it is invertible, and $1$ otherwise). Three assertions are made. First, for every $p$ in the height-one spectrum of $\mathcal{O}_\mathbb{Q}$, the image of this element under `componentAt3`, the $GL_3$-map induced by passing to the finite part and then evaluating in the completion at $p$, is the identity. Secondly, the archimedean component `archComponent3`, the $GL_3$-map induced by projection to the infinite adeles, has [`AutomorphicForm.StandardKernel.realMat`](def/AutomorphicForm_SmoothingKernel.html#L789) — its entrywise real coordinate — equal to `Matrix.of e`. Thirdly, if the columns of $e$ are orthonormal, that is $\sum_{a} e_{a i} e_{a j} = \delta_{ij}$ for all indices $i, j$, then that archimedean component lies in `orth3`, the set of $k \in GL_3(\mathbb{A}_{\mathbb{Q},\infty})$ with $k^{\mathsf{T}}k = 1$.
--
--   This is the elementary bookkeeping identification of the restricted-product decomposition $GL_3(\mathbb{A}_\mathbb{Q}) \cong GL_3(\mathbb{A}_{\mathbb{Q},\infty}) \times GL_3(\mathbb{A}_{\mathbb{Q},f})$ for matrices supported at the infinite place: such a lift is trivial at all finite places, reproduces $e$ archimedeally, and is orthogonal exactly when $e$ is. It serves the archimedean analysis in the Langlands–Tunnell cubic induction, and is used in the constructions of finite-dimensional hulls for the smoothing submodule, of positive polynomial models for the skew form, and in the criterion for archimedean smoothness from continuity, upper-triangular equivariance and orthogonal finiteness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_componentAt3_archRealLift3_eq_one_and_realMat_archComponent3_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.componentAt3_archRealLift3_eq_one_and_realMat_archComponent3_eq
    (e : Fin 3 → Fin 3 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p (WhittakerBlock.archRealLift3 e) = 1) ∧
    AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ (WhittakerBlock.archRealLift3 e)) =
      Matrix.of e ∧
    ((∀ i j : Fin 3, ∑ a : Fin 3, e a i * e a j = if i = j then 1 else 0) →
      archComponent3 (𝓞 ℚ) ℚ (WhittakerBlock.archRealLift3 e) ∈ orth3) := by sorry
