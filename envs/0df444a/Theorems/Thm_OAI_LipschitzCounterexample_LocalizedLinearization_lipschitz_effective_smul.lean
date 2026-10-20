-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_LocalizedLinearization_lipschitz_effective_smul
-- name    : OAI.LipschitzCounterexample.LocalizedLinearization.lipschitz_effective_smul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:52:34.780113+00:00
-- url     : https://prove2.me/theorems/3dd89916-2b4e-42c6-9ab1-4ab22159fb53
-- title:
--   Lipschitz bound for a product with a bounded cutoff
-- statement:
--   Let $p:M\to E$ be $C$-Lipschitz into a normed space and $\varphi:M\to\mathbb R$ be $B$-Lipschitz with $|\varphi|\le A$. Suppose $\|p(x)\|\le P$ wherever $\varphi(x)\ne0$. Then
--   $$
--   x\mapsto\varphi(x)\,p(x)\quad\text{is }(AC+BP)\text{-Lipschitz}.
--   $$
--
--   Only the size of $p$ on the support of $\varphi$ matters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SupportedDuality.lean#L92-L120

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalizedLinearization
universe uM uE
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {E : Type uE} [MetricSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem OAI.LipschitzCounterexample.LocalizedLinearization.lipschitz_effective_smul (p : M → E) (φ : M → ℝ) {A B C P : ℝ≥0}
    (hp : LipschitzWith C p) (hφ : LipschitzWith B φ)
    (hA : ∀ x, |φ x| ≤ A) (hP : ∀ x, φ x ≠ 0 → ‖p x‖ ≤ P) :
    LipschitzWith (A*C+B*P) (fun x => φ x • p x) := by sorry
