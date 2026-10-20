-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_LocalizedLinearization_completely_continuous_of_compact_reduction
-- name    : OAI.LipschitzCounterexample.LocalizedLinearization.completely_continuous_of_compact_reduction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:51:05.435805+00:00
-- url     : https://prove2.me/theorems/9525fdc2-b7f6-4f15-a210-e9669069fa6a
-- title:
--   Locally orthogonal Lipschitz maps linearize to completely continuous operators
-- statement:
--   For a pointed metric space $M$, $\mathcal F(M)$ is its Lipschitz-free space and $\langle\mu,f\rangle$ denotes the pairing of $\mu\in\mathcal F(M)$ with a Lipschitz function $f$ normalized by $f(0)=0$. $\mathcal F(M)$ has compact reduction if every weakly null sequence can be uniformly approximated, to any accuracy, by elements supported on one compact set containing $0$. Let $\mathcal H=\bigl(\bigoplus_n\mathbb R^{\iota_n}\bigr)_{\ell^2}$ be a Hilbert sum of finite-dimensional Euclidean spaces, with coordinates indexed by pairs $(n,a)$; for a set $S$ of coordinates, $P_S$ is the orthogonal projection onto vectors supported in $S$. A map $D:M\to\mathcal H$ is locally orthogonal if for finitely many distinct points $z_i$ there are $r>0$, a block index $l$ and pairwise disjoint coordinate sets $S_i$ with $\mathrm{tail}_l(D(x))$ supported in $S_i$ whenever $d(x,z_i)<r$. Let $M$ be second countable with $\mathcal F(M)$ having compact reduction. If $D:M\to\mathcal H$ is Lipschitz, $D(0)=0$, and locally orthogonal, then its linearization
--   $$
--   \hat D:\mathcal F(M)\to\mathcal H
--   $$
--   is completely continuous: it maps weakly null sequences to norm null sequences.
--
--   Applied to the displacement of the moving-slot map, this gives the complete continuity required in the main construction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/CompleteContinuity.lean#L98-L169

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalizedLinearization
universe uE uM uIndex
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open Filter Set Topology LocalLipschitz CoordinateSpaces LocalGeometry
open scoped NNReal InnerProductSpace
variable {M : Type uM} [MetricSpace M] [Zero M]
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

theorem OAI.LipschitzCounterexample.LocalizedLinearization.completely_continuous_of_compact_reduction [SecondCountableTopology M]
    (hcompact : FreeSpace.HasCompactReduction (M := M))
    (D : M → Hilbert (ι := ι)) {L : ℝ≥0} (hD : LipschitzWith L D) (hD0 : D 0 = 0)
    (hloc : LocalOrthogonality D) : WeakSequences.CompletelyContinuous (FreeSpace.linearize D) := by sorry
