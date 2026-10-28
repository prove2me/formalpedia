-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_local_residual_rule_step_s2
-- name    : OAI.SKGapCutoff.Recipe.local_residual_rule_step_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:52:46.409447+00:00
-- url     : https://prove2.me/theorems/f791e637-166f-42e6-8c82-07460b5e74b1
-- title:
--   OAI.SKGapCutoff.Recipe.local_residual_rule_step_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators`, `open Primary Static`):
--
--   ```lean
--   lemma local_residual_rule_step_s2 (C : FiniteLocalRecipeControl Z j J h Θ w y M Nmax A)
--       (hP : ∀a x,0≤P a x) (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
--       (b : ℕ→ℝ) (hmono : Antitone b)
--       (α : Fin M→κ) (hΘ : ∀a q,Θ a (α q)=fun x=>j*(onsager j (J a) (h a) (q.val+1) x-onsager j (J a) (h a) q.val x)) (k : ℕ) (hkM : k+1<M)
--       (hkA : b k≤A) (hk2 : 2≤b k)
--       (hstep : b (k+1)+4*steinCoefficientBudget |j| *b (k+1)≤b k)
--       (ih : ∀r<k+1,LocalRecipeResidualRule Z Θ w y j J h P M Nmax r (b r)) :
--       LocalRecipeResidualRule Z Θ w y j J h P M Nmax (k+1) (b (k+1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Observables`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.VectorFields` and `OAI.SKGapCutoff.Primary.onsager` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.FiniteLocalRecipeControl`, `OAI.SKGapCutoff.Recipe.LocalRecipeResidualRule` and `OAI.SKGapCutoff.Recipe.steinCoefficientBudget` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** No other item of this split imports it.
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
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {Z : ∀a,Set (Spin (n a))} {Θ : ∀a,κ→Observables (n a)}
variable {w y : ∀a,VectorFields (n a)}

lemma local_residual_rule_step_s2 (C : FiniteLocalRecipeControl Z j J h Θ w y M Nmax A)
    (hP : ∀a x,0≤P a x) (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm)
    (b : ℕ→ℝ) (hmono : Antitone b)
    (α : Fin M→κ) (hΘ : ∀a q,Θ a (α q)=fun x=>j*(onsager j (J a) (h a) (q.val+1) x-onsager j (J a) (h a) q.val x)) (k : ℕ) (hkM : k+1<M)
    (hkA : b k≤A) (hk2 : 2≤b k)
    (hstep : b (k+1)+4*steinCoefficientBudget |j| *b (k+1)≤b k)
    (ih : ∀r<k+1,LocalRecipeResidualRule Z Θ w y j J h P M Nmax r (b r)) :
    LocalRecipeResidualRule Z Θ w y j J h P M Nmax (k+1) (b (k+1)) := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end
