-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_uniform_residual_square_rule_s2
-- name    : OAI.SKGapCutoff.Recipe.uniform_residual_square_rule_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:53:16.251272+00:00
-- url     : https://prove2.me/theorems/f3dd7f7b-bd4a-44c0-b8f8-bd9e0d775cec
-- title:
--   OAI.SKGapCutoff.Recipe.uniform_residual_square_rule_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators`, `open Primary Static`):
--
--   ```lean
--   theorem uniform_residual_square_rule_s2 (C : FiniteRecipeControl j J h M Nmax A)
--       (hP : ∀a x,0≤P a x) (hp : ∀a,∑x,P a x=1)
--       (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
--       (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
--       (b : ℕ→ℝ) (hmono : Antitone b) (pmax : ℕ) (hM : pmax<M)
--       (hA : ∀p≤pmax,b p≤A) (h2 : ∀p≤pmax,2≤b p)
--       (hstep : ∀k<pmax,b (k+1)+4*steinCoefficientBudget |j| *b (k+1)≤b k) :
--       ∀p≤pmax,RecipeSquareResidualRule j J h P M Nmax p (b p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Observables`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.Primary.mag` and `OAI.SKGapCutoff.Static.conditionalMean` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.FiniteRecipeControl`, `OAI.SKGapCutoff.Recipe.RecipeSquareResidualRule` and `OAI.SKGapCutoff.Recipe.steinCoefficientBudget` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** The proof of `OAI.SKGapCutoff.Recipe.gibbs_selected_all_directions_s2` of this split imports it.
-- source:
--   OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ072A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

theorem uniform_residual_square_rule_s2 (C : FiniteRecipeControl j J h M Nmax A)
    (hP : ∀a x,0≤P a x) (hp : ∀a,∑x,P a x=1)
    (hm : ∀a x i,conditionalMean (P a) x i=mag j (J a) (h a) 1 x i)
    (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    (b : ℕ→ℝ) (hmono : Antitone b) (pmax : ℕ) (hM : pmax<M)
    (hA : ∀p≤pmax,b p≤A) (h2 : ∀p≤pmax,2≤b p)
    (hstep : ∀k<pmax,b (k+1)+4*steinCoefficientBudget |j| *b (k+1)≤b k) :
    ∀p≤pmax,RecipeSquareResidualRule j J h P M Nmax p (b p) := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end
