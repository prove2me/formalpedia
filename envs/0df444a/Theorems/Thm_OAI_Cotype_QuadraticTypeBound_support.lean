-- Prove2me | Theorems.Thm_OAI_Cotype_QuadraticTypeBound_support
-- name    : OAI.Cotype.QuadraticTypeBound.support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:09:38.582348+00:00
-- url     : https://prove2.me/theorems/fab75dda-b682-4673-8cfb-5f684029dff9
-- title:
--   Type 2 bounds of length m apply to vectors with m-element support
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Say $X$ has a quadratic type bound of length $m$ with constant $A$ if
--   $$
--   \mathbb E_\varepsilon\Bigl\|\sum_{i=1}^m\varepsilon_ix_i\Bigr\|^2\le A\sum_{i=1}^m\|x_i\|^2
--   $$
--   for all $x_1,\dots,x_m\in X$. If this holds, then the same inequality holds for every family $x_1,\dots,x_N$ that vanishes outside a set of at most $m$ indices.
--
--   So only the number of nonzero vectors matters, not the ambient length $N$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/IndependentSigns.lean#L76-L96

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
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.Cotype.QuadraticTypeBound.support {m N : ℕ} {A : ℝ}
    (h : QuadraticTypeBound X m A) (s : Finset (Fin N)) (hs : s.card ≤ m)
    (x : Fin N → X) (hx : ∀ i, i ∉ s → x i = 0) :
    cubeL2 X (rademacherSum X x)^2 ≤ A*∑ i, ‖x i‖^2 := by sorry
