-- Prove2me | Theorems.Thm_OAI_Cotype_projectionSemigroup_hasDerivAt_zero
-- name    : OAI.Cotype.projectionSemigroup_hasDerivAt_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:58:46.584592+00:00
-- url     : https://prove2.me/theorems/99d1bc43-b787-4d7b-a108-2d46a2db956f
-- title:
--   The derivative of the coordinate semigroup at zero
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. For commuting bounded projections $P_1,\dots,P_m$ on $X$, products are taken in a fixed order, $P_S=\prod_{i\in S}P_i$, and the coordinate semigroup is $T(r)=\prod_i\bigl(P_i+r(1-P_i)\bigr)$. Let $P_1,\dots,P_m$ be commuting bounded operators on a real normed space. Then the map $r\mapsto T(r)$ is differentiable at $r=0$ with
--   $$
--   T'(0)=\sum_{i=1}^m(1-P_i)\prod_{j\ne i}P_j .
--   $$
--
--   This derivative is the linear coefficient of the polynomial $T(r)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ProjectionCoefficientDerivative.lean#L34-L48

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum

open OAI OAI.Cotype
open scoped BigOperators
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem OAI.Cotype.projectionSemigroup_hasDerivAt_zero {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hc : ∀ i j, Commute (P i) (P j)) :
    HasDerivAt (projectionSemigroup P) (projectionLinearCoefficient P) 0 := by sorry
