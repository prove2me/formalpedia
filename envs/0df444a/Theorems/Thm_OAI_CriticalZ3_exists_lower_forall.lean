-- Prove2me | Theorems.Thm_OAI_CriticalZ3_exists_lower_forall
-- name    : OAI.CriticalZ3.exists_lower_forall
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:52:09.637303+00:00
-- url     : https://prove2.me/theorems/eb2c02c4-d562-46ac-9127-372cfe086fd0
-- title:
--   Strict inequalities persist slightly below a positive parameter
-- statement:
--   Let $I$ be finite, $p>0$, and let $g_i:\mathbb R\to\mathbb R$ be continuous with $g_i(p)<\gamma$ for all $i$. Then there is $q\in(p/2,p)$ with
--   $$
--   g_i(q)<\gamma\quad\text{for all }i .
--   $$
--
--   It is applied to the finitely many crossing probabilities as functions of the parameter.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/QuarterFaces.lean#L347-L362

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces

open OAI OAI.CriticalZ3
universe uE uI uV uW
open MeasureTheory ProbabilityTheory Classical
open Filter Topology Classical

theorem OAI.CriticalZ3.exists_lower_forall {I : Type uI} [Finite I] {p γ : ℝ} (hp : 0 < p)
    (g : I → ℝ → ℝ) (hg : ∀ i, Continuous (g i)) (hgp : ∀ i, g i p < γ) :
    ∃ q ∈ Set.Ioo (p/2) p, ∀ i, g i q < γ := by sorry
