-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_correction_pairing_bound
-- name    : OAI.LipschitzCounterexample.CompactWSC.correction_pairing_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:34:14.153393+00:00
-- url     : https://prove2.me/theorems/35088a4a-a03c-4f0e-a6cf-385fd2516b97
-- title:
--   Pairing change caused by damping a test function
-- statement:
--   For smooth $1$-Lipschitz functions $z_i$ on a Hilbert space $H$, the damping factor is $\Delta(x)=\prod_i(1-\|\nabla z_i(x)\|)\in[0,1]$. For molecular data $a$ (coefficients $c_i$, pairs $(p_i,q_i)$), the pairing is $\langle a,f\rangle=\sum_ic_i(f(p_i)-f(q_i))$, the cost is $\sum_i|c_i|\,\|p_i-q_i\|$, and the gradient mass $\mathcal M_a(f)$ integrates $\|\nabla f\|$ along the segments $[q_i,p_i]$ with these weights. Let $f$ be smooth and $1$-Lipschitz, $w$ smooth, and let $a$ be molecular data whose points lie in a convex set $Q$. If $\|\nabla w(x)-\Delta(x)\nabla f(x)\|\le\varepsilon$ on $Q$, then
--   $$
--   \bigl|\langle a,w\rangle-\langle a,f\rangle\bigr|\le\sum_i\mathcal M_a(z_i)+\varepsilon\cdot\mathrm{cost}(a).
--   $$
--
--   Damping by earlier functions changes the pairing only by their gradient mass on the molecule.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/PairingEstimates.lean#L69-L92

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
open Set Filter MeasureTheory FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem OAI.LipschitzCounterexample.CompactWSC.correction_pairing_bound {ι : Type uIndex} (s : Finset ι) (z : ι → Smooth H)
    (hz : ∀ i ∈ s, LipschitzWith 1 (z i).val) (f w : Smooth H)
    (hf : LipschitzWith 1 f.val) (a : MolecularData H) {Q : Set H} (hQ : Convex ℝ Q)
    (ha : ∀ i, a.p i ∈ Q ∧ a.q i ∈ Q) (ε : ℝ)
    (herr : ∀ x ∈ Q, ‖Smooth.grad x w-damping s z x • Smooth.grad x f‖ ≤ ε) :
    |smoothPair a w-smoothPair a f| ≤ (∑ i ∈ s, gradMass a (z i))+ε*a.cost := by sorry
