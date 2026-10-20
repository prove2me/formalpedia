-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_SeparatingStages_finite_slot_locality
-- name    : OAI.LipschitzCounterexample.SeparatingStages.finite_slot_locality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:35:14.330211+00:00
-- url     : https://prove2.me/theorems/36d0b1da-2997-4b4b-b5b7-dcdb94fc17c5
-- title:
--   Local disjointness of slot vectors at finitely many points
-- statement:
--   Let $M=U\oplus_2\ell^2$ with $U=\bigl(\bigoplus_n\mathbb R^{\mathrm{BlockLabel}(n)}\bigr)_{\ell^2}$, where block $n$ has a reserved label and, for each stage $k\le n$, a copy of the stage-$(k+1)$ labels. The slot vector $\mathrm{slot}_n(x)$ is the unit vector obtained by rotating through the stage vectors of block $n$ with angles driven by the slot radius of $x$; the stage-$k$ vectors are normalized bump vectors $G_{k+1}(p(x))$ of the coordinates $p_j(x)=\tanh(x_{(j)})$. For finitely many distinct points $x_i$ of $M$ there are $r>0$ and $l$ such that for $i\ne j$, all blocks $n\ge l$, all $s\in B(x_i,r)$, $t\in B(x_j,r)$ and all labels $a$,
--   $$
--   \mathrm{slot}_n(s)_a=0\quad\text{or}\quad\mathrm{slot}_n(t)_a=0 .
--   $$
--
--   This is the local orthogonality of the moving slots.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/LocalOrthogonality.lean#L167-L205

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.SeparatingStages
universe uI
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set

theorem OAI.LipschitzCounterexample.SeparatingStages.finite_slot_locality {I : Type uI} [Fintype I] (x : I → M) (hx : Function.Injective x) :
    ∃ r : ℝ, 0 < r ∧ ∃ l : ℕ, ∀ i j : I, i ≠ j → ∀ n ≥ l,
      ∀ s ∈ Metric.ball (x i) r, ∀ t ∈ Metric.ball (x j) r,
      ∀ a : BlockLabel n, slot n s a = 0 ∨ slot n t a = 0 := by sorry
