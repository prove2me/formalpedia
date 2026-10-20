-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_exists_smooth_finite_min
-- name    : OAI.LipschitzCounterexample.CompactWSC.exists_smooth_finite_min
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:14:12.870027+00:00
-- url     : https://prove2.me/theorems/04809e24-fd41-475b-b602-2d252d61e6fd
-- title:
--   Smooth 1-Lipschitz lower envelopes on finite sets
-- statement:
--   Let $S$ be a finite subset of a real inner product space $H$ containing $0$, let $f$ be $1$-Lipschitz on $S$, $\delta>0$ and $t\subseteq S$. Then there is a smooth $1$-Lipschitz $g:H\to\mathbb R$ with
--   $$
--   g(q)\ge f(q)-\tfrac{|t|\,\delta}2\ \ (q\in S),\qquad g(p)\le f(p)+\delta\ \ (p\in t).
--   $$
--
--   It is built as an iterated soft minimum of regularized cones.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SmoothHilbert.lean#L131-L177

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

theorem OAI.LipschitzCounterexample.CompactWSC.exists_smooth_finite_min (S : Finset H) (hS : (0 : H) ∈ S)
    (f : H → ℝ) (hf : ∀ p ∈ S, ∀ q ∈ S, |f p-f q| ≤ dist p q)
    (δ : ℝ) (hδ : 0 < δ) (t : Finset H) (ht : t ⊆ S) :
    ∃ g : H → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith 1 g ∧
      (∀ q ∈ S, f q-(t.card : ℝ)*δ/2 ≤ g q) ∧
      (∀ p ∈ t, g p ≤ f p+δ) := by sorry
