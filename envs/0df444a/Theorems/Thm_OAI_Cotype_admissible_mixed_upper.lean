-- Prove2me | Theorems.Thm_OAI_Cotype_admissible_mixed_upper
-- name    : OAI.Cotype.admissible_mixed_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T21:05:09.934707+00:00
-- url     : https://prove2.me/theorems/017db0dd-fdc4-40de-8676-9b9fb5c239fb
-- title:
--   An upper bound for the mixed coefficient of a rank-one supported triple
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Sign matrices are Boolean $m\times m$ matrices; $\mathrm{row}(\sigma)$ and $\mathrm{col}(\tau)$ are the matrices with entries $\sigma_i$ and $\tau_j$, $\oplus$ is XOR, and $\mathrm{sgn}(0)=1$, $\mathrm{sgn}(1)=-1$. A triple $(\Psi,f,g)$ with $\Psi$ on sign matrices and $f,g$ on $\{0,1\}^m$ is scalar admissible with parameters $a,b$ if: all three are odd and bounded by $4$; $\hat f(e_i)=a$ and $\hat g(e_j)=b$ for all unit vectors; and the row and column identities hold, $\mathbb E_\sigma\mathrm{sgn}(\sigma_i)\Psi(\mathrm{row}(\sigma)\oplus S)=a\,g(S_{i\cdot})$ and $\mathbb E_\tau\mathrm{sgn}(\tau_j)\Psi(\mathrm{col}(\tau)\oplus S)=b\,f(S_{\cdot j})$. Let $d(m)=\lceil2\log_2m\rceil$. Let $(\Psi,f,g)$ be scalar admissible with parameters $a,b\ge0$, and suppose $\Psi$ is rank-one supported: $\hat\Psi(P)=0$ whenever $P$ has $\mathbb F_2$-rank at least $2$. Let $d=d(m)$ with $4\le d<m$. Let $R(s,u)=\sum C_{k,l}(\Psi)2^{-kl}s^ku^l$ over $k\le d$ or $l\le d$ be the retained grouped polynomial, $C_{k,l}$ being the sum of Fourier coefficients over $k\times l$ rectangles. Then
--   $$
--   \bigl|\partial_u\partial_sR(0,0)\bigr|\le4d(d+1)\bigl(ma+mb+10\,d(d+1)^2\bigr).
--   $$
--
--   The bound is roughly linear in $ma$ and $mb$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/MixedDerivative.lean#L108-L157

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

open OAI OAI.Cotype
open scoped BigOperators
open Polynomial
variable {m : ℕ}

theorem OAI.Cotype.admissible_mixed_upper {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) (hr : RankOneSupported Ψ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 4 ≤ degreeCutoff m) (hm : degreeCutoff m < m) :
    |(partialS Ψ (degreeCutoff m)).derivative.eval 0| ≤
      4 * (degreeCutoff m : ℝ) * (degreeCutoff m+1) *
        ((m : ℝ)*a + (m : ℝ)*b + 10*(degreeCutoff m : ℝ)*(degreeCutoff m+1)^2) := by sorry
