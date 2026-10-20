-- Prove2me | Theorems.Thm_OAI_Cotype_walsh_paired_frames_orbit
-- name    : OAI.Cotype.walsh_paired_frames_orbit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:33:30.300422+00:00
-- url     : https://prove2.me/theorems/eae1b6f5-6582-48d9-8bfa-b930c0c4d0e3
-- title:
--   Binary frames with equal Walsh pairings are related by a Walsh symmetry
-- statement:
--   Call a pair of permutations $(\sigma,\tau)$ of $\{0,1\}^n$ a Walsh symmetry if $\chi_{\tau(v)}(\sigma(u))=\chi_v(u)$ for all $u,v$. Let $U,U'$ be $r$-tuples and $V,V'$ $s$-tuples of points of $\{0,1\}^n$, each linearly independent over $\mathbb F_2$, with
--   $$
--   \chi_{V_j}(U_i)=\chi_{V'_j}(U'_i)\qquad\text{for all }i,j .
--   $$
--   Then some Walsh symmetry $(\sigma,\tau)$ has $\sigma(U_i)=U'_i$ and $\tau(V_j)=V'_j$ for all $i,j$.
--
--   So Walsh patterns of independent frames depend only on their pairing matrix.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/WalshFrameOrbit.lean#L37-L68

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

open OAI OAI.Cotype
variable {n r s : ℕ}

theorem OAI.Cotype.walsh_paired_frames_orbit (U U' : Fin r → Cube n) (V V' : Fin s → Cube n)
    (hU : BinaryFrame U) (hU' : BinaryFrame U')
    (hV : BinaryFrame V) (hV' : BinaryFrame V')
    (hpair : ∀ i j, character (V j) (U i) = character (V' j) (U' i)) :
    ∃ g : WalshSymmetry n,
      (∀ i, primalSymmetry g (U i) = U' i) ∧ ∀ j, dualSymmetry g (V j) = V' j := by sorry
