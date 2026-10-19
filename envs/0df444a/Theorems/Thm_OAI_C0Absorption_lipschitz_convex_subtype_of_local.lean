-- Prove2me | Theorems.Thm_OAI_C0Absorption_lipschitz_convex_subtype_of_local
-- name    : OAI.C0Absorption.lipschitz_convex_subtype_of_local
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T21:59:28.634424+00:00
-- url     : https://prove2.me/theorems/a15db1fe-acc7-41e9-8cec-be4877081d04
-- title:
--   Local Lipschitz bounds on convex sets are global
-- statement:
--   Let $B$ be a convex subset of a real normed space and $f:B\to Y$ continuous into a pseudo-metric space. If $f$ is locally $K$-Lipschitz, i.e. each point of $B$ has a neighbourhood in $B$ on which $d(f(x),f(y))\le K\|x-y\|$, then
--   $$
--   f\ \text{is}\ K\text{-Lipschitz on all of}\ B .
--   $$
--
--   Lipschitz constants can be checked locally on convex domains such as the unit ball of $c_0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Localization.lean#L71-L93

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

theorem OAI.C0Absorption.lipschitz_convex_subtype_of_local {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
    {B : Set E} (hB : Convex ℝ B) {f : B → Y} {K : ℝ≥0}
    (hf : Continuous f)
    (hloc : ∀ x, ∀ᶠ y in nhds x, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith K f := by sorry
