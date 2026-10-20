-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_CoordinateSpaces_sum_projection_sq_le
-- name    : OAI.LipschitzCounterexample.CoordinateSpaces.sum_projection_sq_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:40:15.027934+00:00
-- url     : https://prove2.me/theorems/be6a4ab2-a5d6-41df-be02-014986eb938f
-- title:
--   Bessel inequality for disjoint coordinate projections
-- statement:
--   Let $\mathcal H=\bigl(\bigoplus_n\mathbb R^{\iota_n}\bigr)_{\ell^2}$ be a Hilbert sum of finite-dimensional Euclidean spaces, with coordinates indexed by pairs $(n,a)$; for a set $S$ of coordinates, $P_S$ is the orthogonal projection onto vectors supported in $S$. For finitely many pairwise disjoint coordinate sets $S_i$ and any $x\in\mathcal H$,
--   $$
--   \sum_i\|P_{S_i}x\|^2\le\|x\|^2 .
--   $$
--
--   This is used to show that only finitely many points can carry a large local Lipschitz constant.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SeparableCoordinates.lean#L132-L158

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CoordinateSpaces
universe uIndex uI uE uM
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

theorem OAI.LipschitzCounterexample.CoordinateSpaces.sum_projection_sq_le {I : Type uI} [Fintype I] (S : I → Set (Σ n, ι n))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (x : Hilbert (ι := ι)) :
    ∑ i, ‖projection (S i) x‖^2 ≤ ‖x‖^2 := by sorry
