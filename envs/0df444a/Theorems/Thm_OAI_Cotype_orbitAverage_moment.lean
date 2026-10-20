-- Prove2me | Theorems.Thm_OAI_Cotype_orbitAverage_moment
-- name    : OAI.Cotype.orbitAverage_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:34:22.605802+00:00
-- url     : https://prove2.me/theorems/a7d56de5-6c1c-41ef-8158-aa876be4af69
-- title:
--   Orbit averaging preserves prescribed moments
-- statement:
--   A normed space $Z$ satisfies the fixed cotype bound of length $m$ with constant $D$ if $\bigl(\sum_{i\le m}\|z_i\|^2\bigr)^{1/2}\le D\bigl(\mathbb E\|\sum_{i\le m}\varepsilon_iz_i\|^2\bigr)^{1/2}$ for all $z_1,\dots,z_m\in Z$. The $i$-th moment of $F:\{0,1\}^m\to Z$ is $\hat F_i=\mathbb E_u\,\varepsilon_i(u)F(u)$, and $\|F\|_{L_2}=(\mathbb E\|F\|^2)^{1/2}$. Let a finite group $\Gamma$ act on a set $I$ and by linear isometries $\rho$ on a real normed space $X$. Let $x:I\to X^m$ be equivariant, $x_{h\cdot a,i}=\rho(h)x_{a,i}$, and let $P_a:\{0,1\}^m\to X$ have moments $\widehat{(P_a)}_i=c\,x_{a,i}$. Define the orbit average
--   $$
--   \bar P_a(\varepsilon)=\mathbb E_{g\in\Gamma}\,\rho(g)\,P_{g^{-1}a}(\varepsilon).
--   $$
--   Then $\bar P_a$ again has moments $c\,x_{a,i}$ for all $a$ and $i$.
--
--   Symmetrizing a family of lifts keeps their moments while making them equivariant.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/EquivariantLifts.lean#L41-L61

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

open OAI OAI.Cotype
open scoped BigOperators
variable {Γ I X : Type*} [Group Γ] [Fintype Γ] [MulAction Γ I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.Cotype.orbitAverage_moment {m : ℕ} (ρ : Γ →* (X ≃ₗᵢ[ℝ] X))
    (x : I → Fin m → X) (hx : ∀ h a i, x (h • a) i = ρ h (x a i))
    (c : ℝ) (P : I → Cube m → X)
    (hP : ∀ a i, moment X (P a) i = c • x a i) (a : I) (i : Fin m) :
    moment X (fun ε => orbitAverage ρ (fun b => P b ε) a) i = c • x a i := by sorry
