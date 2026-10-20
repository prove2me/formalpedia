-- Prove2me | Theorems.Thm_OAI_Cotype_GrowthPairingData_tagged_coefficient_extraction
-- name    : OAI.Cotype.GrowthPairingData.tagged_coefficient_extraction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T21:13:02.358888+00:00
-- url     : https://prove2.me/theorems/c272e28d-15c6-4ee8-8ade-8476a0116199
-- title:
--   Extracting Fourier coefficients of pattern pairings by tagged lifts
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Fix growth pairing data for a nonzero operator $T:X\to Y$ in dimension $n$, with constant $\gamma>\omega_n(T)/2$, where $\omega_j$ denotes the Walsh norm. The data consist of unit families $x(u)$, $y(v)$ with $y(v)(\widetilde Tx(u))=\gamma\chi_v(u)$ for an $\ell_2$-amplification $\widetilde T$ of $T$ with the same Walsh norms. They also include equivariant unit-ball lifts $P_U(\varepsilon)$, $Z_V(\delta)$ of $m$-tuples, whose moments are fixed multiples of $x(U_i)$ and $y(V_i)$. The pattern pairing $\Psi_S(\varepsilon,\delta)=Z_V(\delta)(\widetilde TP_U(\varepsilon))$ is taken for frames $U,V$ with Walsh pairing pattern $S$, a Boolean $m\times m$ matrix. Here $n=k+2m$. For $u,v\in(\{0,1\}^k)^m$ let $F(u,v)$ be the sign matrix with entries the $\mathbb F_2$ pairings $\langle v_j,u_i\rangle$. Let $\mathcal P(\varepsilon,u)$ be the lift of the tagged primal tuple built from $u$, and let $\mathcal Z(P,\delta,v)=\mathbb E_D\,\chi_P(D)\,Z_{V(v,D)}(\delta)$ average the tagged dual lifts against the character $\chi_P$. Then
--   $$
--   \mathcal Z(P,\delta,v)\bigl(\widetilde T\mathcal P(\varepsilon,u)\bigr)=\widehat{\Psi_\cdot(\varepsilon,\delta)}(P)\;\chi_P\bigl(F(u,v)\bigr).
--   $$
--
--   A single Fourier coefficient of the pattern pairing becomes an honest operator pairing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/TaggedCoefficient.lean#L51-L69

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
import Definitions.Def_OAI_Analysis_Cotype_ProjectionDerivatives
import Definitions.Def_OAI_Analysis_Cotype_MixedDerivative
import Definitions.Def_OAI_Analysis_Cotype_CoefficientCompactness
import Definitions.Def_OAI_Analysis_Cotype_GrowthScalarData
import Definitions.Def_OAI_Analysis_Cotype_TaggedCoefficient

open OAI OAI.Cotype OAI.Cotype.GrowthPairingData
open scoped BigOperators
variable {k m : ℕ}
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {T : X →L[ℝ] Y} {Dg Df : ℝ}
variable (d : GrowthPairingData T (k+m+m) m Dg Df)

theorem OAI.Cotype.GrowthPairingData.tagged_coefficient_extraction (hn : m+m ≤ k+m+m) (P : SignMatrix m)
    (ε δ : Cube m) (u v : Fin m → Cube k) :
    d.coefficientDual P δ v (d.amplifiedOperator (d.coefficientPrimal ε u)) =
      fourier (fun S => d.patternPairing hn S ε δ) P * character P (freePairingPattern u v) := by sorry
