-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_ConstructionPrefix_extend
-- name    : OAI.LipschitzCounterexample.CompactWSC.ConstructionPrefix.extend
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:37:25.487695+00:00
-- url     : https://prove2.me/theorems/e3f396f6-b27a-4a9e-8021-4728f9031367
-- title:
--   Construction prefixes can be extended by one step
-- statement:
--   Triangular rows are finite sequences of pairs (smooth $1$-Lipschitz test $f_j$ with $f_j(0)=0$, molecular data $a_i$ supported in $K$ of cost $\le C$ and within $\rho$ of the sequence $\mu$) with $\langle a_i,f_j\rangle\ge4\alpha$ for $j\le i$ and $|\langle a_i,f_j\rangle|\le\alpha$ for $i<j$; a family of rows is rich if it contains rows of every length. A construction prefix of length $n$ consists of smooth functions $z_i,w_i$ and row items $a_i$ ($i<n$) with $z_i$ $1$-Lipschitz, $\langle a_i,z_i\rangle\ge\alpha$, small masses $\mathcal M_{a_i}(z_j)\le\eta_j$ for $j<i$, damped gradients $\|\nabla w_i-\Delta_{<i}\nabla z_i\|\le\varepsilon_i$ on $Q$, and still rich restricted rows. For compact $Q$, $C\ge0$, $\alpha>0$ and positive tolerances, every prefix of length $n$ extends to a prefix of length $n+1$:
--   $$
--   (z_i,w_i,a_i)_{i<n}\ \longmapsto\ (z_i,w_i,a_i)_{i\le n}.
--   $$
--
--   Iterating it yields an infinite detecting sequence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/DetectingSequence.lean#L37-L100

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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MolecularApproximation
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothCalculus
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_EnergyEstimates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothRows
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BlockSelection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SmoothMultiplier
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_DetectingSequence

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC OAI.LipschitzCounterexample.CompactWSC.ConstructionPrefix
universe uH
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {K Q : Set H} {C ρ α : ℝ} {μ : ℕ → Space H} {ε η : ℕ → ℝ}

theorem OAI.LipschitzCounterexample.CompactWSC.ConstructionPrefix.extend (hQ : IsCompact Q) (hC : 0 ≤ C) (hα : 0 < α)
    (hε : ∀ i, 0 < ε i) (hη : ∀ i, 0 < η i) {n : ℕ}
    (p : ConstructionPrefix K Q C ρ α μ ε η n) :
    ∃ q : ConstructionPrefix K Q C ρ α μ ε η (n+1),
      ∀ i < n, q.z i = p.z i ∧ q.w i = p.w i ∧ q.a i = p.a i := by sorry
