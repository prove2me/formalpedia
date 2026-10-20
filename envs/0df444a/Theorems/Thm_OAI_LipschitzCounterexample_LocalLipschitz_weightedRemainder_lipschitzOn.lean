-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_LocalLipschitz_weightedRemainder_lipschitzOn
-- name    : OAI.LipschitzCounterexample.LocalLipschitz.weightedRemainder_lipschitzOn
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:47:51.962843+00:00
-- url     : https://prove2.me/theorems/a772a105-2ed1-4c12-9b01-174813348881
-- title:
--   Lipschitz bound for the weighted remainder
-- statement:
--   Let $d:M\to\mathbb R$ be $A$-Lipschitz on $O$, let $\varphi_j$ ($j$ in a finite set $I$) be $B$-Lipschitz with $\sum_j\varphi_j(x)\in[0,1]$, and let $|d|\le\varepsilon$ on $K$ and at the points $z_j$. Then the weighted remainder
--   $$
--   x\mapsto d(x)-\sum_j\bigl(d(x)-d(z_j)\bigr)\varphi_j(x)
--   $$
--   is $(A+2|I|B\varepsilon)$-Lipschitz on $K\cap O$.
--
--   So cutting $d$ off near the points $z_j$ costs little when $d$ is small there.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/CompactLipschitz.lean#L121-L154

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalLipschitz
universe uM uI
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

theorem OAI.LipschitzCounterexample.LocalLipschitz.weightedRemainder_lipschitzOn (d : M → ℝ) (z : I → M) (φ : I → M → ℝ)
    {K O : Set M} {A B ε : ℝ≥0}
    (hd : LipschitzOnWith A d O) (hφ : ∀ j, LipschitzWith B (φ j))
    (hsum : ∀ x, (∑ j,φ j x) ∈ Icc (0 : ℝ) 1)
    (hsmall : ∀ x ∈ K, |d x| ≤ ε) (hzsmall : ∀ j, |d (z j)| ≤ ε) :
    LipschitzOnWith (A+2*Fintype.card I*B*ε) (weightedRemainder d z φ) (K ∩ O) := by sorry
