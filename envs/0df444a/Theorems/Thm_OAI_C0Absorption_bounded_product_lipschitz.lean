-- Prove2me | Theorems.Thm_OAI_C0Absorption_bounded_product_lipschitz
-- name    : OAI.C0Absorption.bounded_product_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:07:42.063934+00:00
-- url     : https://prove2.me/theorems/7c5fa2fd-ee9f-41b5-92dd-aa219ca998bb
-- title:
--   Products of bounded Lipschitz functions
-- statement:
--   Let $f$ be $K$-Lipschitz with $|f|\le A$ and $g$ be $L$-Lipschitz with $|g|\le B$ on a pseudo-metric space. Then
--   $$
--   fg\ \text{is}\ (AL+BK)\text{-Lipschitz}.
--   $$
--
--   This is used for products of generated test functions with tail factors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Tests.lean#L186-L201

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

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem OAI.C0Absorption.bounded_product_lipschitz {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {K L A B : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfB : ∀ x, |f x| ≤ A) (hgB : ∀ x, |g x| ≤ B) :
    LipschitzWith (A*L+B*K) (fun x => f x*g x) := by sorry
