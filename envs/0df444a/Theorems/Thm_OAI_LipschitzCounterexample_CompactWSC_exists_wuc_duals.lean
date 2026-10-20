-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_exists_wuc_duals
-- name    : OAI.LipschitzCounterexample.CompactWSC.exists_wuc_duals
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:43:57.485615+00:00
-- url     : https://prove2.me/theorems/3f924986-d714-4a9f-8c26-1ad56e63495f
-- title:
--   Weakly unconditionally Cauchy functionals on compactly supported free spaces
-- statement:
--   Triangular rows are finite sequences of pairs (smooth $1$-Lipschitz test $f_j$ with $f_j(0)=0$, molecular data $a_i$ supported in $K$ of cost $\le C$ and within $\rho$ of the sequence $\mu$) with $\langle a_i,f_j\rangle\ge4\alpha$ for $j\le i$ and $|\langle a_i,f_j\rangle|\le\alpha$ for $i<j$; a family of rows is rich if it contains rows of every length. Let $0\in K\subseteq Q$ with $Q$ compact and convex, $C\ge0$, $\alpha>0$, and suppose the triangular rows are rich. Then there are functionals $T_i$ on $\mathcal F(H)$ with $\|T_i\|\le2$ and row items $a_i$ with $T_i(\text{vector of }a_i)\ge\alpha/2$, such that for all $u\in\mathcal F_K(H)$ and signs $|c_i|\le1$,
--   $$
--   \Bigl|\sum_{i<n}c_i\,T_i(u)\Bigr|\le2\|u\| .
--   $$
--
--   Such a family maps $\mathcal F_K(H)$ boundedly into $\ell^1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/WUCDuals.lean#L73-L94

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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WUCFunctions
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WUCDuals

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uH
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSpace_1
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSpace_1
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedAddCommGroupSubtypeSpaceMemSubmoduleRealSupported_1
attribute [local instance] OAI.LipschitzCounterexample.CompactWSC.instNormedSpaceRealSubtypeSpaceMemSubmoduleSupported_1
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem OAI.LipschitzCounterexample.CompactWSC.exists_wuc_duals {K Q : Set H} (h0 : (0:H) ∈ K)
    (hQ : IsCompact Q) (hQc : Convex ℝ Q) (hKQ : K ⊆ Q)
    {C ρ α : ℝ} {μ : ℕ → Space H} (hC : 0 ≤ C) (hα : 0 < α)
    (hRich : (triangularRows K C ρ α μ).Rich) :
    ∃ (T : ℕ → Space H →L[ℝ] ℝ) (a : ℕ → RowItem K C ρ μ),
      (∀ i, ‖T i‖ ≤ 2) ∧ (∀ i, α/2 ≤ T i (a i).a.vector) ∧
      ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) → ∀ u : Space H, u ∈ supported K →
        |∑ i ∈ Finset.range n, c i*T i u| ≤ 2*‖u‖ := by sorry
