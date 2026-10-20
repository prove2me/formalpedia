-- Prove2me | Theorems.Thm_OAI_Cotype_odd_rank_one_support
-- name    : OAI.Cotype.odd_rank_one_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:27:36.260387+00:00
-- url     : https://prove2.me/theorems/44a1b515-b849-4e5d-917e-eb8ce464e076
-- title:
--   Rank-one frequencies of odd matrix functions are odd rectangles
-- statement:
--   Let $f$ be a real function on Boolean $\iota\times\kappa$ matrices that is odd: $f(\bar S)=-f(S)$, where $\bar S$ flips every entry. Let $P$ be a frequency, also a Boolean matrix, with $\hat f(P)\ne0$ and rank at most $1$ over $\mathbb F_2$. Then there are finite sets $s\subseteq\iota$ and $t\subseteq\kappa$ with
--   $$
--   P=s\times t,\qquad|s|\ \text{and}\ |t|\ \text{odd}.
--   $$
--
--   So the low-rank Fourier support of an odd function consists of odd-by-odd rectangles.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/BinaryRank.lean#L65-L83

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

open OAI OAI.Cotype
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem OAI.Cotype.odd_rank_one_support {f : ((ι × κ) → Bool) → ℝ} (hf : IsOdd f)
    {P : (ι × κ) → Bool} (hcoef : fourier f P ≠ 0)
    (hP : (binaryMatrix P).rank ≤ 1) :
    ∃ (s : Finset ι) (t : Finset κ),
      Odd s.card ∧ Odd t.card ∧ rectangle s t = P := by sorry
