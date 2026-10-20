-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_gradEnergy_midpoint
-- name    : OAI.LipschitzCounterexample.CompactWSC.gradEnergy_midpoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:18:51.004528+00:00
-- url     : https://prove2.me/theorems/59e0fc51-7f6f-4433-a1f8-57bb98ecd1ea
-- title:
--   Midpoint identity for the gradient energy
-- statement:
--   For a real Hilbert space $H$, molecular data $a$ consist of coefficients $c_i$ and point pairs $(p_i,q_i)$, with cost $\sum_i|c_i|\,\|p_i-q_i\|$. For a smooth $f$ on $H$, the gradient energy and mass of $a$ are
--   $$
--   \mathcal E_a(f)=\sum_i|c_i|\,\|p_i-q_i\|\int_0^1\|\nabla f(\gamma_i(t))\|^2dt,\qquad \mathcal M_a(f)=\sum_i|c_i|\,\|p_i-q_i\|\int_0^1\|\nabla f(\gamma_i(t))\|dt ,
--   $$
--   where $\gamma_i(t)=q_i+t(p_i-q_i)$. For smooth $f,g$ the energy satisfies the parallelogram-type identity
--   $$
--   \mathcal E_a\Bigl(\tfrac{f+g}2\Bigr)=\frac{\mathcal E_a(f)+\mathcal E_a(g)}2-\frac{\mathcal E_a(f-g)}4 .
--   $$
--
--   This makes the energy a valid quadratic quantity for the dyadic averaging argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SmoothCalculus.lean#L131-L146

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uH
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]
open FreeSpace

theorem OAI.LipschitzCounterexample.CompactWSC.gradEnergy_midpoint (a : MolecularData H) (f g : Smooth H) :
    gradEnergy a ((1/2:ℝ) • (f+g)) =
      (gradEnergy a f+gradEnergy a g)/2-gradEnergy a (f-g)/4 := by sorry
