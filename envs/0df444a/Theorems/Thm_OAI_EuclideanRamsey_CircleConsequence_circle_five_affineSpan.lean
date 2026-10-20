-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_circle_five_affineSpan
-- name    : OAI.EuclideanRamsey.CircleConsequence.circle_five_affineSpan
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:28:21.209091+00:00
-- url     : https://prove2.me/theorems/71da14b4-1e4d-445e-b042-a9cef3f01d1a
-- title:
--   Five distinct points on a circle span the plane
-- statement:
--   Let $a_0,\dots,a_4$ be distinct points of $\mathbb R^2$ with $|a_i-c|=r$ for all $i$. Then their affine span is the whole plane:
--   $$
--   \operatorname{aff}\{a_0,\dots,a_4\}=\mathbb R^2 .
--   $$
--
--   Full affine span is one of the hypotheses under which the field criterion characterizes Ramsey configurations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CircleSpan.lean#L7-L44

import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows

open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.CircleConsequence

theorem OAI.EuclideanRamsey.CircleConsequence.circle_five_affineSpan (a : Fin 5 → Space 2)
    (ha : Function.Injective a) (c : Space 2) (r : ℝ)
    (hc : ∀ i, dist (a i) c = r) : affineSpan ℝ (Set.range a) = ⊤ := by sorry
