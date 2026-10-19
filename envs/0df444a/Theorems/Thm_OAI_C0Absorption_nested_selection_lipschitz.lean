-- Prove2me | Theorems.Thm_OAI_C0Absorption_nested_selection_lipschitz
-- name    : OAI.C0Absorption.nested_selection_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:14:52.831433+00:00
-- url     : https://prove2.me/theorems/ce6e6499-7cff-4e4c-82d7-ee230a57fb8a
-- title:
--   Selecting a compatible subsequence of nested localized products
-- statement:
--   On a convex set, let $F_i=u_i\,b_i$ be $K$-Lipschitz products with continuous $u_i$ and $K_b$-Lipschitz $b_i$. Suppose $u_i\equiv e_i$ on open sets $C_i$, the supports of later $u_j$ eventually lie in each $C_i$, and $|e_i|K_b\to0$. Then there is a subsequence $\varphi$ such that for every $n$ and all signs,
--   $$
--   x\longmapsto\sum_{i<n}\pm F_{\varphi(i)}(x)\ \text{is}\ (K+1)\text{-Lipschitz}.
--   $$
--
--   Nested localization and decaying plateau values make the products compatible.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Selection.lean#L108-L143

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

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem OAI.C0Absorption.nested_selection_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Convex ℝ S) (u b : ℕ → S → ℝ) (C : ℕ → Set S) (e : ℕ → ℝ)
    (K Kb : ℝ≥0) (hu : ∀ i, Continuous (u i)) (hb : ∀ i, LipschitzWith Kb (b i))
    (hF : ∀ i, LipschitzWith K (fun x => u i x*b i x))
    (hC : ∀ i, IsOpen (C i)) (hc : ∀ i, ∀ x ∈ C i, u i x=e i)
    (hnest : ∀ i, ∀ᶠ j in atTop, tsupport (u j) ⊆ C i)
    (hsmall : Tendsto (fun i => |e i| *(Kb : ℝ)) atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
        LipschitzWith (K+1) (fun x => ∑ i, ε i * (u (φ i) x*b (φ i) x)) := by sorry
