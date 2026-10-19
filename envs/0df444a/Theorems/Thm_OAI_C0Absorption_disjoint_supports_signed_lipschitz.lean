-- Prove2me | Theorems.Thm_OAI_C0Absorption_disjoint_supports_signed_lipschitz
-- name    : OAI.C0Absorption.disjoint_supports_signed_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:01:23.274764+00:00
-- url     : https://prove2.me/theorems/b3eb5f4b-af69-4f96-a3cc-f104cc2cb183
-- title:
--   Signed sums of Lipschitz functions with disjoint supports
-- statement:
--   Let $B$ be a convex subset of a real normed space, and let $f_1,\dots,f_k$ be $K$-Lipschitz real functions on $B$ with pairwise disjoint closed supports. Then for every choice of signs $\varepsilon_i=\pm1$,
--   $$
--   x\longmapsto\sum_i\varepsilon_if_i(x)\ \text{is}\ K\text{-Lipschitz}.
--   $$
--
--   Functions with disjoint supports form admissible lists with the same constant.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Localization.lean#L100-L139

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

theorem OAI.C0Absorption.disjoint_supports_signed_lipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E} (hB : Convex ℝ B)
    {ι : Type*} [Fintype ι] (f : ι → B → ℝ) (K : ℝ≥0)
    (hf : ∀ i, LipschitzWith K (f i))
    (hdisj : Pairwise (fun i j => Disjoint (tsupport (f i)) (tsupport (f j))))
    (ε : ι → ℝ) (hε : ∀ i, |ε i| = 1) :
    LipschitzWith K (fun x => ∑ i, ε i * f i x) := by sorry
