-- Prove2me | Theorems.Thm_OAI_C0Absorption_compatible_detectors_false
-- name    : OAI.C0Absorption.compatible_detectors_false
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:20:25.627593+00:00
-- url     : https://prove2.me/theorems/1aa864e7-c114-4962-bc6e-300ecd35cf7d
-- title:
--   Compatible detectors exclude bounded signed sums
-- statement:
--   Let $Z$ be the completion of the molecules on a metric space under the selected norm built from test classes $L_h$. Let $(m_i)$ in $Z$ have bounded signed sums, $\|\sum\pm m_i\|\le M$. Let tests $F_i\in L_h$ be compatible, meaning every finite signed sum $\sum\pm F_i$ is $K$-Lipschitz, and suppose they detect the sequence:
--   $$
--   |\langle F_i,m_i\rangle|\ge\delta>0 .
--   $$
--   Then this situation is impossible.
--
--   A sequence equivalent to the $c_0$ basis cannot be seen by one compatible family of tests.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Operations.lean#L36-L83

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem OAI.C0Absorption.compatible_detectors_false {S : Type*} [MetricSpace S]
    (L : ℕ → Set (S → ℝ)) (o : S)
    (m : ℕ → TestSpace L o) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → S → ℝ) (h : ℕ) (K : ℝ≥0) (hF : ∀ i, F i ∈ L h)
    (hLip : ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
      LipschitzWith K (fun s => ∑ i, ε i*F i s))
    {δ : ℝ} (hδ : 0 < δ) (hd : ∀ i, δ ≤ |completedPairing L o (F i) (m i)|) : False := by sorry
