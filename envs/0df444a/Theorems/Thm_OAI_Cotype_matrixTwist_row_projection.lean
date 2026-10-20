-- Prove2me | Theorems.Thm_OAI_Cotype_matrixTwist_row_projection
-- name    : OAI.Cotype.matrixTwist_row_projection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:54:02.187228+00:00
-- url     : https://prove2.me/theorems/8271ce3e-3c97-42c3-9e83-b5bd25f535a2
-- title:
--   Row projections of the matrix twist
-- statement:
--   Sign matrices are Boolean $m\times m$ matrices; $\mathrm{row}(\sigma)$ is the matrix with entries $\sigma_i$ in row $i$, $S_i$ denotes row $i$ of $S$, and $\oplus$ is entrywise XOR. Let $\Phi(S,\varepsilon,\delta)$ and $\psi(s,\delta)$ be real functions, with $S$ a sign matrix and $s,\varepsilon,\delta\in\{0,1\}^m$, and let $a\in\mathbb R$. With $\mathrm{sgn}(0)=1$ and $\mathrm{sgn}(1)=-1$, suppose that for all $S,\delta,i$ the moment $\mathbb E_\varepsilon \mathrm{sgn}(\varepsilon_i)\Phi(S,\varepsilon,\delta)$ equals $a\,\psi(S_i,\delta)$. Let $\tilde\Phi(S)=\mathbb E_{\varepsilon,\delta}\Phi(\mathrm{row}(\varepsilon)\oplus\mathrm{col}(\delta)\oplus S,\varepsilon,\delta)$ be the matrix twist, $\tilde\psi$ the vector twist of $\psi$, and $\mathcal R_i$ the row projection. Then
--   $$
--   (\mathcal R_i\tilde\Phi)(S)=a\,\tilde\psi_{\mathrm{odd}}(S_i).
--   $$
--
--   Row projections of the twisted matrix function reduce to the twisted row slice.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/PatternProjections.lean#L50-L91

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
import Definitions.Def_OAI_Analysis_Cotype_GrowthTuplePairing
import Definitions.Def_OAI_Analysis_Cotype_PatternPairing
import Definitions.Def_OAI_Analysis_Cotype_TaggedFrames
import Definitions.Def_OAI_Analysis_Cotype_CoefficientTarget
import Definitions.Def_OAI_Analysis_Cotype_DampedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_GroupedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ProjectionCoefficients
import Definitions.Def_OAI_Analysis_Cotype_PatternNormalization
import Definitions.Def_OAI_Analysis_Cotype_PatternProjections

open OAI OAI.Cotype
variable {m : ℕ}

theorem OAI.Cotype.matrixTwist_row_projection (Φ : SignMatrix m → Cube m → Cube m → ℝ)
    (ψ : Cube m → Cube m → ℝ) (a : ℝ)
    (hm : ∀ S δ i, moment ℝ (fun ε => Φ S ε δ) i = a * ψ (fun j => S (i,j)) δ)
    (i : Fin m) (S : SignMatrix m) :
    rowProjection (matrixTwist Φ) i S = a * oddPart (vectorTwist ψ) (fun j => S (i,j)) := by sorry
