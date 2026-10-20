-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_SeparatingStages_D_local_orthogonality
-- name    : OAI.LipschitzCounterexample.SeparatingStages.D_local_orthogonality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:41:03.291891+00:00
-- url     : https://prove2.me/theorems/7efe9025-b8ab-4732-b32d-5276c886ddee
-- title:
--   The displacement of the moving-slot map is locally orthogonal
-- statement:
--   Let $h:M\to U$ be the moving-slot bijection on $M=U\oplus_2\ell^2$ and $D(x)=h(x)-x_U$. For finitely many distinct points $x_i$ there are $r>0$, a block index $l$ and pairwise disjoint sets $S_i$ of coordinates in blocks $\ge l$ such that
--   $$
--   d(y,x_i)<r\ \Longrightarrow\ \mathrm{tail}_l\bigl(D(y)\bigr)\ \text{is supported in }S_i .
--   $$
--
--   This is the local orthogonality hypothesis needed for complete continuity of the linearized displacement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SeparableCoordinates.lean#L186-L214

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.SeparatingStages
universe uIndex uI uE uM
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set CoordinateSpaces

theorem OAI.LipschitzCounterexample.SeparatingStages.D_local_orthogonality {I : Type uI} [Fintype I] (x : I → M) (hx : Function.Injective x) :
    ∃ r : ℝ, 0 < r ∧ ∃ l : ℕ, ∃ S : I → Set (Σ n, BlockLabel n),
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
      (∀ i a, a ∈ S i → l ≤ a.1) ∧
      (∀ i y, y ∈ Metric.ball (x i) r → tailCLM l (D y) ∈ space (S i)) := by sorry
