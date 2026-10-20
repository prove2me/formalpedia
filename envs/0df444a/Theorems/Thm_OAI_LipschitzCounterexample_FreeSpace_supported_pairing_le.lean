-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_supported_pairing_le
-- name    : OAI.LipschitzCounterexample.FreeSpace.supported_pairing_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:42:40.791216+00:00
-- url     : https://prove2.me/theorems/c2f89034-93ce-494e-a459-a85a97bb783e
-- title:
--   Pairings with supported free-space elements see only the local Lipschitz constant
-- statement:
--   For a pointed metric space $M$, $\mathcal F(M)$ is its Lipschitz-free space and $\langle\mu,f\rangle$ denotes the pairing of $\mu\in\mathcal F(M)$ with a Lipschitz function $f$ normalized by $f(0)=0$. $\mathcal F(M)$ has compact reduction if every weakly null sequence can be uniformly approximated, to any accuracy, by elements supported on one compact set containing $0$. Let $K\subseteq M$ contain the base point, and let $f$ be Lipschitz on $M$ and $C$-Lipschitz on $K$. Then for every $\mu$ in the closed span of $\{\delta_x:x\in K\}$,
--   $$
--   |\langle\mu,f\rangle|\le C\,\|\mu\| .
--   $$
--
--   Only the behaviour of $f$ on $K$ matters for elements supported on $K$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SeparableCoordinates.lean#L253-L269

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
universe uIndex uI uE uM
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped Topology NNReal
open Filter Set
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem OAI.LipschitzCounterexample.FreeSpace.supported_pairing_le {K : Set M} (hK : (0 : M) ∈ K)
    (f : M → ℝ) {C L : ℝ≥0} (hf : LipschitzWith L f) (hC : LipschitzOnWith C f K)
    (μ : Space M) (hμ : μ ∈ supported K) :
    |LocalizedLinearization.test (LocalizedLinearization.normalized f hf) μ| ≤ C * ‖μ‖ := by sorry
