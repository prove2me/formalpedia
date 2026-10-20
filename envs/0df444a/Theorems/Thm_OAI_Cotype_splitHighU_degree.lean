-- Prove2me | Theorems.Thm_OAI_Cotype_splitHighU_degree
-- name    : OAI.Cotype.splitHighU_degree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:59:27.376292+00:00
-- url     : https://prove2.me/theorems/5a5ce03f-9059-4fa0-93f0-a2bc8829ebba
-- title:
--   The high Chebyshev part has low degree in the other variable
-- statement:
--   Sign matrices are Boolean $m\times m$ matrices; $\mathrm{row}(\sigma)$ and $\mathrm{col}(\tau)$ are the matrices with entries $\sigma_i$ and $\tau_j$, $\oplus$ is XOR, and $\mathrm{sgn}(0)=1$, $\mathrm{sgn}(1)=-1$. A triple $(\Psi,f,g)$ with $\Psi$ on sign matrices and $f,g$ on $\{0,1\}^m$ is scalar admissible with parameters $a,b$ if: all three are odd and bounded by $4$; $\hat f(e_i)=a$ and $\hat g(e_j)=b$ for all unit vectors; and the row and column identities hold, $\mathbb E_\sigma\mathrm{sgn}(\sigma_i)\Psi(\mathrm{row}(\sigma)\oplus S)=a\,g(S_{i\cdot})$ and $\mathbb E_\tau\mathrm{sgn}(\tau_j)\Psi(\mathrm{col}(\tau)\oplus S)=b\,f(S_{\cdot j})$. Let $d(m)=\lceil2\log_2m\rceil$. For a function $f$ on sign matrices, let $\mathrm{ret}_{k,l}=C_{k,l}(f)2^{-kl}$ when $k\le d$ or $l\le d$, and $0$ otherwise. For $s\in\mathbb R$ consider the polynomial in $u$
--   $$
--   H_s(u)=\sum_{k,l}\mathrm{ret}_{k,l}\,\bigl(s^k-L_d(X^k)(s)\bigr)\,u^l ,
--   $$
--   where $L_d$ keeps the Chebyshev modes of degree at most $d$. Then $\deg H_s\le d$.
--
--   The part of the retained polynomial that is high in $s$ is automatically low in $u$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/BivariateSplit.lean#L125-L139

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
import Definitions.Def_OAI_Analysis_Cotype_DeletedTail
import Definitions.Def_OAI_Analysis_Cotype_ChebyshevBounds
import Definitions.Def_OAI_Analysis_Cotype_ChebyshevTruncation
import Definitions.Def_OAI_Analysis_Cotype_BivariateSplit

open OAI OAI.Cotype
open scoped BigOperators
open Polynomial Polynomial.Chebyshev
variable {m : ℕ}

theorem OAI.Cotype.splitHighU_degree (f : SignMatrix m → ℝ) (d : ℕ) (s : ℝ) :
    (splitHighU f d s).degree ≤ d := by sorry
