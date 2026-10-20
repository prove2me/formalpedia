-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_CompactWSC_gradEnergy_le_cost
-- name    : OAI.LipschitzCounterexample.CompactWSC.gradEnergy_le_cost
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:20:38.181817+00:00
-- url     : https://prove2.me/theorems/a06dbc5d-0b81-41bd-aee7-9320e2d0fb5c
-- title:
--   Gradient energy of a 1-Lipschitz function is at most the molecular cost
-- statement:
--   For a real Hilbert space $H$, molecular data $a$ consist of coefficients $c_i$ and point pairs $(p_i,q_i)$, with cost $\sum_i|c_i|\,\|p_i-q_i\|$. For a smooth $f$ on $H$, the gradient energy and mass of $a$ are
--   $$
--   \mathcal E_a(f)=\sum_i|c_i|\,\|p_i-q_i\|\int_0^1\|\nabla f(\gamma_i(t))\|^2dt,\qquad \mathcal M_a(f)=\sum_i|c_i|\,\|p_i-q_i\|\int_0^1\|\nabla f(\gamma_i(t))\|dt ,
--   $$
--   where $\gamma_i(t)=q_i+t(p_i-q_i)$. If $f$ is smooth and $1$-Lipschitz, then
--   $$
--   \mathcal E_a(f)\le\sum_i|c_i|\,\|p_i-q_i\| ,
--   $$
--   the cost of the molecular data.
--
--   So the energy is controlled by the cost alone for $1$-Lipschitz tests.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/EnergyEstimates.lean#L21-L33

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uH
open scoped ContDiff BigOperators NNReal Topology
open Set Filter MeasureTheory FreeSpace
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem OAI.LipschitzCounterexample.CompactWSC.gradEnergy_le_cost (a : MolecularData H) (f : Smooth H)
    (hf : LipschitzWith 1 (f : H → ℝ)) : gradEnergy a f ≤ a.cost := by sorry
