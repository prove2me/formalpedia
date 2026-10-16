-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Polar_exists_normalizer_equiv
-- name    : OAI.PermanentBorder.Polar.exists_normalizer_equiv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:12:50.050934+00:00
-- url     : https://prove2.me/theorems/a5918270-70e1-4e1f-8451-d371254c17ad
-- title:
--   A nonzero linear form is the first coordinate of some linear automorphism
-- statement:
--   Let $\iota$ be a finite set and $\iota_\ast=\{\ast\}\sqcup\iota$. For every nonzero vector $l\in\mathbb{C}^{\iota_\ast}$ there is a continuous linear automorphism $e$ of $\mathbb{C}^{\iota_\ast}$ whose $\ast$-coordinate is the linear form defined by $l$:
--   $$
--   \exists\,e\in GL\big(\mathbb{C}^{\iota_\ast}\big)\quad\forall\,y\in\mathbb{C}^{\iota_\ast}:\qquad e(y)_\ast=\sum_{j\in\iota_\ast}l_j\,y_j .
--   $$
--
--   In the coordinates $e(y)$, the affine hyperplane $\{\sum_jl_jy_j=1\}$ becomes $\{e(y)_\ast=1\}$ and is parametrized by the remaining $|\iota|$ coordinates. This is used to turn the roots of a homogeneous system in the chart $\sum_jl_jy_j=1$ into zeros of a square system on affine space $\mathbb{C}^{|\iota|}$.
--
--   **Formalization Note** $e$ is a `ContinuousLinearEquiv` of `Option ι → ℂ`, and the coordinate $\ast$ is `none`. In finite dimension every linear automorphism is automatically continuous.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/RankTransfer.lean#L380-L399

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer

open OAI OAI.PermanentBorder OAI.PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem OAI.PermanentBorder.Polar.exists_normalizer_equiv (l : Option ι → ℂ) (hl : l ≠ 0) :
    ∃ e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ),
      ∀ y, e y none = ∑ j, l j * y j := by sorry
