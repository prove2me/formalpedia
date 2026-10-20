-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_exists_smooth_finite_approx
-- name    : OAI.LipschitzCounterexample.CompactWSC.exists_smooth_finite_approx
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:14:54.834023+00:00
-- url     : https://prove2.me/theorems/f67419ca-3e69-4795-bd6a-0b292a764931
-- title:
--   Smooth 1-Lipschitz approximation of Lipschitz data on finite sets
-- statement:
--   Let $S$ be a finite subset of a real inner product space $H$ containing $0$, and let $f$ be $1$-Lipschitz on $S$ with $f(0)=0$. Then for every $\varepsilon>0$ there is a smooth $1$-Lipschitz $g:H\to\mathbb R$ with $g(0)=0$ and
--   $$
--   |g(p)-f(p)|<\varepsilon\quad(p\in S).
--   $$
--
--   Smooth test functions therefore suffice to evaluate finitely supported elements of free spaces over Hilbert spaces.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SmoothHilbert.lean#L179-L202

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothHilbert

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uH uX
open Filter Topology
open scoped NNReal ContDiff
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem OAI.LipschitzCounterexample.CompactWSC.exists_smooth_finite_approx (S : Finset H) (hS : (0 : H) ∈ S)
    (f : H → ℝ) (hf0 : f 0 = 0)
    (hf : ∀ p ∈ S, ∀ q ∈ S, |f p-f q| ≤ dist p q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : H → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith 1 g ∧ g 0 = 0 ∧
      ∀ p ∈ S, |g p-f p| < ε := by sorry
