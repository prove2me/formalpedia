-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_LocalizedLinearization_shrinking_tests
-- name    : OAI.LipschitzCounterexample.LocalizedLinearization.shrinking_tests
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:30:21.854453+00:00
-- url     : https://prove2.me/theorems/adb6a375-9d62-491a-8168-a0bb0ca12526
-- title:
--   Weakly null free-space sequences vanish on shrinking local tests
-- statement:
--   Let $\mu_i$ be weakly null in the free space $\mathcal F(M)$. Let $f_i$ be uniformly $C$-Lipschitz functions vanishing at a point $z$ and outside the balls $B(z,r_i)$, where $r_i>0$ and $r_i\to0$. Then
--   $$
--   \bigl\langle\mu_i,\ f_i-f_i(0)\bigr\rangle\to0 .
--   $$
--
--   This expresses that weakly null sequences in free spaces carry no mass concentrating at a single point.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/Localization.lean#L359-L448

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalizedLinearization
universe uM uV
open Filter Topology
open scoped NNReal ENNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem OAI.LipschitzCounterexample.LocalizedLinearization.shrinking_tests (z : M) {μ : ℕ → FreeSpace.Space M}
    (hw : WeakSequences.WeakNull μ) (r : ℕ → ℝ≥0) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto (fun i => (r i : ℝ)) atTop (𝓝 0))
    (f : ℕ → M → ℝ) {C : ℝ≥0} (hf : ∀ i, LipschitzWith C (f i))
    (hfz : ∀ i, f i z = 0) (hfs : ∀ i x, (r i : ℝ) ≤ dist x z → f i x = 0) :
    Tendsto (fun i => test (normalized (f i) (hf i)) (μ i)) atTop (𝓝 0) := by sorry
