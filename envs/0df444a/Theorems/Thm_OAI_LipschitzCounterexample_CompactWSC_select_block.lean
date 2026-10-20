-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_select_block
-- name    : OAI.LipschitzCounterexample.CompactWSC.select_block
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:25:50.216058+00:00
-- url     : https://prove2.me/theorems/b16c7ac4-e086-4094-8b3c-72c20df9635f
-- title:
--   Selecting a test function with small energy on later rows
-- statement:
--   Triangular rows are finite sequences of pairs (smooth $1$-Lipschitz test $f_j$ with $f_j(0)=0$, molecular data $a_i$ supported in $K$ of cost $\le C$ and within $\rho$ of the sequence $\mu$) with $\langle a_i,f_j\rangle\ge4\alpha$ for $j\le i$ and $|\langle a_i,f_j\rangle|\le\alpha$ for $i<j$, where $\langle a,f\rangle=\sum_ic_i(f(p_i)-f(q_i))$. A family of rows is rich if it contains rows of every length. Suppose the rows restricted to items satisfying $P$ are rich, $\alpha>0$, $S\subseteq H$ is finite and $\varepsilon>0$. Then there are a smooth $1$-Lipschitz $z$ with $z(0)=0$ and an item $a$ with $P(a)$ and $\langle a,z\rangle\ge\alpha$. Moreover the rows of items $b$ with $P(b)$ and
--   $$
--   \mathcal E_b(z)+\sum_{p\in S}z(p)^2<\varepsilon
--   $$
--   remain rich.
--
--   Repeating this selection builds the detecting sequence of test functions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/BlockSelection.lean#L86-L164

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uH
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
variable {H : Type uH} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

theorem OAI.LipschitzCounterexample.CompactWSC.select_block {K : Set H} {C ρ α : ℝ} {μ : ℕ → Space H}
    (hα : 0 < α) (P : RowItem K C ρ μ → Prop)
    (hRich : ((triangularRows K C ρ α μ).restrict P).Rich)
    (S : Finset H) {ε : ℝ} (hε : 0 < ε) :
    ∃ (z : Smooth H) (a : RowItem K C ρ μ), LipschitzWith 1 z.val ∧ z.val 0 = 0 ∧
      P a ∧ α ≤ smoothPair a.a z ∧
      ((triangularRows K C ρ α μ).restrict
        (fun b => P b ∧ augmentedEnergy b.a S 1 z < ε)).Rich := by sorry
