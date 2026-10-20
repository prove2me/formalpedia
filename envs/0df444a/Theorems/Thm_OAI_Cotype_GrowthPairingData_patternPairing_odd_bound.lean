-- Prove2me | Theorems.Thm_OAI_Cotype_GrowthPairingData_patternPairing_odd_bound
-- name    : OAI.Cotype.GrowthPairingData.patternPairing_odd_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:42:59.982318+00:00
-- url     : https://prove2.me/theorems/793b5cbc-8587-4131-8c30-3c6e40aa046a
-- title:
--   Odd parts of pattern pairings are bounded by the Walsh norm
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Fix growth pairing data for a nonzero operator $T:X\to Y$ in dimension $n=k+2m$. These consist of unit families $x(u)$ and $y(v)$, $u,v\in\{0,1\}^n$, with $y(v)(\widetilde Tx(u))=\gamma\,\chi_v(u)$, where $\widetilde T$ is an $\ell_2$-amplification of $T$ with the same Walsh norms $\omega_j$. They also include unit-ball lifts $P_U(\varepsilon)$ and $Z_V(\delta)$, indexed by $m$-tuples $U,V$ of cube points, whose coordinate moments are fixed multiples of $x(U_i)$ and $y(V_i)$, and which are equivariant under Walsh symmetries. The odd part of a function $h$ on a cube is $h_{\mathrm{odd}}(S)=\frac12(h(S)-h(\bar S))$, where $\bar S$ flips every coordinate. Let $\Psi_S(\varepsilon,\delta)$ be the pattern pairing: the pairing $Z_V(\delta)(\widetilde TP_U(\varepsilon))$ for frames $U,V$ whose Walsh pairing matrix is the sign matrix $S$. Then for all $S$ and $\varepsilon,\delta\in\{0,1\}^m$,
--   $$
--   \bigl|\tfrac12\bigl(\Psi_S(\varepsilon,\delta)-\Psi_{\bar S}(\varepsilon,\delta)\bigr)\bigr|\le\omega_k(T).
--   $$
--
--   The odd part of the pattern pairing is controlled by the Walsh norm in the smaller dimension $k$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/OddPatternBounds.lean#L61-L74

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

open OAI OAI.Cotype OAI.Cotype.GrowthPairingData
open scoped BigOperators
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {k m : ℕ} {T : X →L[ℝ] Y} {Dg Df : ℝ}
variable (d : GrowthPairingData T (k+m+m) m Dg Df)

theorem OAI.Cotype.GrowthPairingData.patternPairing_odd_bound (hn : m+m ≤ k+m+m)
    (S : Fin m × Fin m → Bool) (ε δ : Cube m) :
    |oddPart (fun S => d.patternPairing hn S ε δ) S| ≤ walshNorm k T := by sorry
