-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_exists_detecting_sequence
-- name    : OAI.LipschitzCounterexample.CompactWSC.exists_detecting_sequence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:39:29.922036+00:00
-- url     : https://prove2.me/theorems/daf59776-e70f-453c-ad43-aba0b2d46129
-- title:
--   Existence of a detecting sequence of damped test functions
-- statement:
--   Triangular rows are finite sequences of pairs (smooth $1$-Lipschitz test $f_j$ with $f_j(0)=0$, molecular data $a_i$ supported in $K$ of cost $\le C$ and within $\rho$ of the sequence $\mu$) with $\langle a_i,f_j\rangle\ge4\alpha$ for $j\le i$ and $|\langle a_i,f_j\rangle|\le\alpha$ for $i<j$; a family of rows is rich if it contains rows of every length. For smooth $1$-Lipschitz functions $z_i$ on a Hilbert space $H$, the damping factor is $\Delta(x)=\prod_i(1-\|\nabla z_i(x)\|)\in[0,1]$. For molecular data $a$ (coefficients $c_i$, pairs $(p_i,q_i)$), the pairing is $\langle a,f\rangle=\sum_ic_i(f(p_i)-f(q_i))$, the cost is $\sum_i|c_i|\,\|p_i-q_i\|$, and the gradient mass $\mathcal M_a(f)$ integrates $\|\nabla f\|$ along the segments $[q_i,p_i]$ with these weights. If the triangular rows are rich, $Q$ is compact, $C\ge0$, $\alpha>0$ and $\varepsilon_i,\eta_i>0$, then there are infinite sequences $z_i,w_i$ of smooth functions and row items $a_i$ with:
--   - $z_i$ $1$-Lipschitz, $z_i(0)=w_i(0)=0$, $\langle a_i,z_i\rangle\ge\alpha$;
--   - $\mathcal M_{a_i}(z_j)\le\eta_j$ for $j<i$;
--   - on $Q$,
--   $$
--   \Bigl\|\nabla w_i-\prod_{j<i}\bigl(1-\|\nabla z_j\|\bigr)\nabla z_i\Bigr\|\le\varepsilon_i .
--   $$
--
--   The damping makes the gradients of later functions avoid the regions where earlier ones are steep.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/DetectingSequence.lean#L104-L165

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uH
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem OAI.LipschitzCounterexample.CompactWSC.exists_detecting_sequence {K Q : Set H} (hQ : IsCompact Q)
    {C ρ α : ℝ} {μ : ℕ → Space H} (hC : 0 ≤ C) (hα : 0 < α)
    (hRich : (triangularRows K C ρ α μ).Rich) (ε η : ℕ → ℝ)
    (hε : ∀ i, 0 < ε i) (hη : ∀ i, 0 < η i) :
    ∃ (z w : ℕ → Smooth H) (a : ℕ → RowItem K C ρ μ),
      (∀ i, LipschitzWith 1 (z i).val) ∧
      (∀ i, (z i).val 0 = 0 ∧ (w i).val 0 = 0) ∧
      (∀ i, α ≤ smoothPair (a i).a (z i)) ∧
      (∀ i j, j < i → gradMass (a i).a (z j) ≤ η j) ∧
      ∀ i x, x ∈ Q →
        ‖Smooth.grad x (w i)-damping (Finset.range i) z x • Smooth.grad x (z i)‖ ≤ ε i := by sorry
