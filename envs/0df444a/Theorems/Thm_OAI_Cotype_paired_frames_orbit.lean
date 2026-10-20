-- Prove2me | Theorems.Thm_OAI_Cotype_paired_frames_orbit
-- name    : OAI.Cotype.paired_frames_orbit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:32:51.935784+00:00
-- url     : https://prove2.me/theorems/2bc82106-0f19-4846-97c6-28af83c48430
-- title:
--   Paired frames with equal pairings lie in one orbit
-- statement:
--   Let $\Bbbk$ be a field and $E$ a finite-dimensional $\Bbbk$-vector space. Let $(U_i)_{i\in\iota}$ and $(U'_i)_{i\in\iota}$ be linearly independent families in $E$, and $(V_j)_{j\in\kappa}$, $(V'_j)_{j\in\kappa}$ linearly independent families in $E^*$, with
--   $$
--   V_j(U_i)=V'_j(U'_i)\qquad\text{for all }i,j .
--   $$
--   Then there is a linear automorphism $H$ of $E$ with $HU_i=U'_i$ for all $i$ and $V'_j\circ H=V_j$ for all $j$.
--
--   The pairing matrix is the only invariant of a pair of frames under the general linear group.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/FrameOrbit.lean#L50-L66

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

open OAI OAI.Cotype
open scoped BigOperators
variable {𝕜 : Type*} [Field 𝕜]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

theorem OAI.Cotype.paired_frames_orbit [FiniteDimensional 𝕜 E]
    (U U' : ι → E) (V V' : κ → Module.Dual 𝕜 E)
    (hU : LinearIndependent 𝕜 U) (hU' : LinearIndependent 𝕜 U')
    (hV : LinearIndependent 𝕜 V) (hV' : LinearIndependent 𝕜 V')
    (hpair : ∀ i j, V j (U i) = V' j (U' i)) :
    ∃ H : E ≃ₗ[𝕜] E, (∀ i, H (U i) = U' i) ∧ ∀ j x, V' j (H x) = V j x := by sorry
