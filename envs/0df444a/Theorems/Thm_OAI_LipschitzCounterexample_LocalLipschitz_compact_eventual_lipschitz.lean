-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_LocalLipschitz_compact_eventual_lipschitz
-- name    : OAI.LipschitzCounterexample.LocalLipschitz.compact_eventual_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:47:11.823051+00:00
-- url     : https://prove2.me/theorems/3ade8a7e-998c-4a09-b565-5ab9803e03fe
-- title:
--   Local eventual Lipschitz bounds on a compact set globalize
-- statement:
--   Let $R_i:M\to\mathbb R$, $K\subseteq M$ compact and $C>0$. Assume $R_i\to0$ uniformly on $K$, and every $p\in K$ has an open neighbourhood $V$ on which $R_i$ is eventually $C$-Lipschitz on $K\cap V$. Then eventually
--   $$
--   R_i\ \text{is }C\text{-Lipschitz on }K .
--   $$
--
--   So local control near every point of a compact set gives global control on that set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/CompactLipschitz.lean#L66-L99

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalLipschitz
universe uM uI
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

theorem OAI.LipschitzCounterexample.LocalLipschitz.compact_eventual_lipschitz (R : ℕ → M → ℝ) {K : Set M} (hK : IsCompact K)
    {C : ℝ≥0} (hC : 0 < C)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ K, |R i x| < ε)
    (hloc : ∀ p ∈ K, ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      ∀ᶠ i in atTop, LipschitzOnWith C (R i) (K ∩ V)) :
    ∀ᶠ i in atTop, LipschitzOnWith C (R i) K := by sorry
