-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_selection_step
-- name    : OAI.LipschitzCounterexample.CompactWSC.selection_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:34:58.38625+00:00
-- url     : https://prove2.me/theorems/e2ee49fb-b344-4af9-bee1-9ab81ac74065
-- title:
--   One step of the damped selection
-- statement:
--   Triangular rows are finite sequences of pairs (smooth $1$-Lipschitz test $f_j$ with $f_j(0)=0$, molecular data $a_i$ supported in $K$ of cost $\le C$ and within $\rho$ of the sequence $\mu$) with $\langle a_i,f_j\rangle\ge4\alpha$ for $j\le i$ and $|\langle a_i,f_j\rangle|\le\alpha$ for $i<j$; a family of rows is rich if it contains rows of every length. For smooth $1$-Lipschitz functions $z_i$ on a Hilbert space $H$, the damping factor is $\Delta(x)=\prod_i(1-\|\nabla z_i(x)\|)\in[0,1]$. For molecular data $a$ (coefficients $c_i$, pairs $(p_i,q_i)$), the pairing is $\langle a,f\rangle=\sum_ic_i(f(p_i)-f(q_i))$, the cost is $\sum_i|c_i|\,\|p_i-q_i\|$, and the gradient mass $\mathcal M_a(f)$ integrates $\|\nabla f\|$ along the segments $[q_i,p_i]$ with these weights. Let $Q$ be compact, $C\ge0$, $\alpha>0$, suppose the rows restricted to $P$ are rich, and let $z_i$ be finitely many smooth $1$-Lipschitz functions. For all $\varepsilon,\eta>0$ there are smooth $f,w$ with $f$ $1$-Lipschitz, $f(0)=w(0)=0$, and an item $a$ with $P(a)$ and $\langle a,f\rangle\ge\alpha$, such that
--   $$
--   \|\nabla w-\Delta\nabla f\|\le\varepsilon\ \text{on }Q .
--   $$
--   Moreover the rows of items $b$ with $P(b)$ and $\mathcal M_b(f)\le\eta$ remain rich.
--
--   This is one step of the inductive construction of the detecting sequence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SelectionStep.lean#L13-L80

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uH uIndex
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem OAI.LipschitzCounterexample.CompactWSC.selection_step {K Q : Set H} (hQ : IsCompact Q)
    {C ρ α : ℝ} {μ : ℕ → Space H} (hC : 0 ≤ C) (hα : 0 < α)
    (P : RowItem K C ρ μ → Prop)
    (hRich : ((triangularRows K C ρ α μ).restrict P).Rich)
    {ι : Type uIndex} [Fintype ι] (z : ι → Smooth H) (hz : ∀ i, LipschitzWith 1 (z i).val)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ (f w : Smooth H) (a : RowItem K C ρ μ),
      LipschitzWith 1 f.val ∧ f.val 0 = 0 ∧ w.val 0 = 0 ∧
      P a ∧ α ≤ smoothPair a.a f ∧
      (∀ x ∈ Q, ‖Smooth.grad x w-damping Finset.univ z x • Smooth.grad x f‖ ≤ ε) ∧
      ((triangularRows K C ρ α μ).restrict (fun b => P b ∧ gradMass b.a f ≤ η)).Rich := by sorry
