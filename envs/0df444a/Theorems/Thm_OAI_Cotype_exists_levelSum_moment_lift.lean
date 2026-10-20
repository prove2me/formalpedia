-- Prove2me | Theorems.Thm_OAI_Cotype_exists_levelSum_moment_lift
-- name    : OAI.Cotype.exists_levelSum_moment_lift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:41:06.735844+00:00
-- url     : https://prove2.me/theorems/88a1b98e-74f3-454a-88ba-fdf95959ddce
-- title:
--   Moment lifts in the weighted level sum
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. A normed space $Z$ satisfies the fixed cotype bound of length $m$ with constant $D$ if $\bigl(\sum_{i\le m}\|z_i\|^2\bigr)^{1/2}\le D\bigl(\mathbb E\|\sum_{i\le m}\varepsilon_iz_i\|^2\bigr)^{1/2}$ for all $z_1,\dots,z_m\in Z$. The $i$-th moment of $F:\{0,1\}^m\to Z$ is $\hat F_i=\mathbb E_u\,\varepsilon_i(u)F(u)$, and $\|F\|_{L_2}=(\mathbb E\|F\|^2)^{1/2}$. Let $A_0\subseteq A_1\subseteq\dots$ be finite-dimensional subspaces of a real Banach space $X$. Let $\Lambda=\ell_2(A_0,A_1,\dots)$ be their $\ell_2$-sum and $W:\Lambda\to X$ the weighted map $W(z)=\sum_l2^{-l}z_l$, of norm at most $2$. Suppose each pair $A_l\subseteq A_{l+1}$ has the lifting property with constant $3D$: every $z_1,\dots,z_m\in A_l$ have a lift $H:\{0,1\}^m\to A_{l+1}$ with moments $z_i$ and $\|H\|_{L_2}\le3D(\sum\|z_i\|^2)^{1/2}$. Then for every $z_1,\dots,z_m\in\Lambda$ there is $H:\{0,1\}^m\to\Lambda$ with $W(\hat H_i)=W(z_i)$ for all $i$ and
--   $$
--   \|H\|_{L_2}\le6D\Bigl(\sum_i\|z_i\|^2\Bigr)^{1/2}.
--   $$
--
--   Moments are matched only after applying $W$, which leaves room to shift each level up by one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/CompactMomentAssembly.lean#L19-L92

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
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_FrameFeasibility
import Definitions.Def_OAI_Analysis_Cotype_EquivariantLifts
import Definitions.Def_OAI_Analysis_Cotype_DualAction
import Definitions.Def_OAI_Analysis_Cotype_EquivariantPairing
import Definitions.Def_OAI_Analysis_Cotype_FrameLifts
import Definitions.Def_OAI_Analysis_Cotype_L2MomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteLevelTower
import Definitions.Def_OAI_Analysis_Cotype_WeightedCompact
import Definitions.Def_OAI_Analysis_Cotype_CompactQuotient

open OAI OAI.Cotype
open scoped BigOperators ENNReal
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (A : ℕ → Submodule ℝ X)

theorem OAI.Cotype.exists_levelSum_moment_lift {m : ℕ} {D : ℝ} (hD : 0 < D)
    (hL : ∀ l, FiniteLevelLift m D (A l) (A (l+1))) (z : Fin m → LevelSum A) :
    ∃ H : Cube m → LevelSum A,
      (∀ i, weightedMap A (moment (LevelSum A) H i) = weightedMap A (z i)) ∧
      cubeL2 (LevelSum A) H ≤ 6 * D * Real.sqrt (∑ i, ‖z i‖^2) := by sorry
