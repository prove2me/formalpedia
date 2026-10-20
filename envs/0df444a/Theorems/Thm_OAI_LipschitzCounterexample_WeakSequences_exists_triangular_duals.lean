-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_exists_triangular_duals
-- name    : OAI.LipschitzCounterexample.WeakSequences.exists_triangular_duals
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:19:52.200737+00:00
-- url     : https://prove2.me/theorems/6ef52f13-4a9f-483b-9756-b5a8ca671882
-- title:
--   Triangular systems of functionals for a non-convergent weakly Cauchy sequence
-- statement:
--   Let $u_n$ be a sequence in a real normed space $E$ converging weak$^*$ to $\varphi\in E^{**}$, with $\varphi$ at distance at least $d>0$ from the canonical image of $E$. Then for every $N$ there are norm-one functionals $f_0,\dots,f_{N-1}$ with $\varphi(f_j)>d/2$, and indices $v_0,\dots,v_{N-1}$, such that
--   $$
--   f_j(u_{v_i})>\tfrac d4\ \ (j\le i),\qquad f_j(u_{v_i})=0\ \ (i<j).
--   $$
--
--   The matrix $(f_j(u_{v_i}))$ is thus lower triangular with large entries on and below the diagonal.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/TriangularDuals.lean#L13-L57

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.WeakSequences
universe uE
open scoped Topology BigOperators
open Filter Set
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem OAI.LipschitzCounterexample.WeakSequences.exists_triangular_duals {u : ℕ → E} {φ : (E →L[ℝ] ℝ) →L[ℝ] ℝ}
    (hφ : ∀ f, Tendsto (fun n => f (u n)) atTop (𝓝 (φ f)))
    {d : ℝ} (hd : 0 < d)
    (hfar : ∀ x : E, d ≤ ‖φ-NormedSpace.inclusionInDoubleDual ℝ E x‖) (N : ℕ) :
    ∃ (f : Fin N → E →L[ℝ] ℝ) (v : Fin N → ℕ),
      (∀ j, ‖f j‖ = 1 ∧ d/2 < φ (f j)) ∧
      (∀ i j, j ≤ i → d/4 < f j (u (v i))) ∧
      (∀ i j, i < j → f j (u (v i)) = 0) := by sorry
