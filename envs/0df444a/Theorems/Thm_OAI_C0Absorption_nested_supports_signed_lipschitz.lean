-- Prove2me | Theorems.Thm_OAI_C0Absorption_nested_supports_signed_lipschitz
-- name    : OAI.C0Absorption.nested_supports_signed_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:01:55.235885+00:00
-- url     : https://prove2.me/theorems/4fbceee1-dea0-47e9-b316-3f2692de98a5
-- title:
--   Signed sums of products with nested supports
-- statement:
--   Let $B$ be convex, and let $F_i=u_i\,b_i$ ($i<n$) be $K$-Lipschitz products, with $b_i$ being $K_i$-Lipschitz and $u_i$ continuous. Let $C_i$ be open sets on which $u_i\equiv e_i$ is constant, with nested supports $\operatorname{supp}u_j\subseteq C_i$ for $i<j$. Then for all signs $\varepsilon_i=\pm1$,
--   $$
--   x\longmapsto\sum_i\varepsilon_iu_i(x)b_i(x)\ \text{is}\ \Bigl(K+\sum_i|e_i|K_i\Bigr)\text{-Lipschitz}.
--   $$
--
--   Nested localized tests still form admissible lists.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Localization.lean#L141-L213

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open Set Filter Topology

theorem OAI.C0Absorption.nested_supports_signed_lipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E} (hB : Convex ℝ B)
    (n : ℕ) (u b : Fin n → B → ℝ) (e : Fin n → ℝ)
    (C : Fin n → Set B) (K : ℝ≥0) (Kb : Fin n → ℝ≥0)
    (_hu : ∀ i, Continuous (u i)) (hb : ∀ i, LipschitzWith (Kb i) (b i))
    (hF : ∀ i, LipschitzWith K (fun x => u i x * b i x))
    (hC : ∀ i, IsOpen (C i)) (hc : ∀ i, ∀ x ∈ C i, u i x = e i)
    (hnest : ∀ i j, i < j → tsupport (u j) ⊆ C i)
    (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) :
    LipschitzWith (K + ∑ i, ‖e i‖₊ * Kb i)
      (fun x => ∑ i, ε i * (u i x * b i x)) := by sorry
