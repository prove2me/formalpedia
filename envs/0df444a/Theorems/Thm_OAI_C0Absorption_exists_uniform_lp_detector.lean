-- Prove2me | Theorems.Thm_OAI_C0Absorption_exists_uniform_lp_detector
-- name    : OAI.C0Absorption.exists_uniform_lp_detector
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T21:55:35.177868+00:00
-- url     : https://prove2.me/theorems/57c3c4cf-5183-4f53-8836-41ab4ec1d580
-- title:
--   Large lp norm and bounded lq norm force a large coordinate
-- statement:
--   Let $1\le q<p$ (finite exponents), $a>0$ and $B>0$. Then there is $\delta>0$ such that for every $n$ and every $x\in\mathbb R^n$,
--   $$
--   \|x\|_p\ge a\ \text{and}\ \|x\|_q\le B\implies|x_i|>\delta\ \text{for some }i .
--   $$
--
--   A vector cannot have large $\ell^p$ norm and small $\ell^q$ norm without a large coordinate, uniformly in the dimension.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Lists.lean#L152-L179

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset

theorem OAI.C0Absorption.exists_uniform_lp_detector (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : 0 < p.toReal) (hq : 0 < q.toReal) (hqp : q.toReal < p.toReal)
    (a B : ℝ) (ha : 0 < a) (hB : 0 < B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (x : Fin n → ℝ),
      a ≤ ‖WithLp.toLp p x‖ → ‖WithLp.toLp q x‖ ≤ B →
      ∃ i, δ < |x i| := by sorry
