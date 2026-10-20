-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_LocalLipschitz_uniform_zero_on_compact
-- name    : OAI.LipschitzCounterexample.LocalLipschitz.uniform_zero_on_compact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:45:44.506987+00:00
-- url     : https://prove2.me/theorems/e633e737-2837-42e5-932e-ccd48846dec4
-- title:
--   Equi-Lipschitz pointwise null sequences converge uniformly on compacts
-- statement:
--   Let $f_i:M\to\mathbb R$ be uniformly $L$-Lipschitz functions on a metric space with $f_i(x)\to0$ for every $x$. Then for every compact $K\subseteq M$ and $\varepsilon>0$, eventually
--   $$
--   |f_i(x)|<\varepsilon\quad\text{for all }x\in K .
--   $$
--
--   This is the Arzelà–Ascoli type step of the localization argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/LocalLipschitz.lean#L80-L106

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalLipschitz
universe uM uN uB uIndex
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} [MetricSpace M]

theorem OAI.LipschitzCounterexample.LocalLipschitz.uniform_zero_on_compact (f : ℕ → M → ℝ) {L : ℝ≥0}
    (hf : ∀ i, LipschitzWith L (f i))
    (hpoint : ∀ x, Tendsto (fun i => f i x) atTop (𝓝 0))
    {K : Set M} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ x ∈ K, |f i x| < ε := by sorry
