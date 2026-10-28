-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_gibbs_selected_all_directions_s2
-- name    : OAI.SKGapCutoff.Recipe.gibbs_selected_all_directions_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:52:24.048785+00:00
-- url     : https://prove2.me/theorems/d4f2472c-587e-457d-a2be-d52a88e19567
-- title:
--   OAI.SKGapCutoff.Recipe.gibbs_selected_all_directions_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators`, `open Primary Static`):
--
--   ```lean
--   lemma gibbs_selected_all_directions_s2 (d : ℕ) (hρ : 0<ρ)
--       (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
--       (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
--       (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 d 0) B W C (d+1) (2*d) (J a)) :
--       ∃A:ℝ,0≤A ∧ ∀a (e:Fin (N a)→ℝ),vectorNorm e≤1→∀f:Observables (N a),
--         |∑x,fieldGibbs (J a) (h a) x*(f x)^2*
--           (∑k∈Finset.range (d-1),cutoffWeight (fun l=>residualCutoff ρ j (J a) (h a) l x) k*
--             (∑i,(spin x i-mag j (J a) (h a) (k+2) x i)*e i))|≤
--         A*starSquared (fieldGibbs (J a) (h a)) f
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Observables`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.fieldGibbs`, `OAI.SKGapCutoff.spin`, `OAI.SKGapCutoff.Primary.mag` and `OAI.SKGapCutoff.Recipe.vectorNorm` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.cutoffWeight` (definitions bundle `OAIQ072A001` of this split); `OAI.SKGapCutoff.Recipe.RecipeMatrixEvent`, `OAI.SKGapCutoff.Recipe.residualCoefficientBudget`, `OAI.SKGapCutoff.Recipe.residualCutoff` and `OAI.SKGapCutoff.Static.starSquared` (definitions bundle `OAIQ072A002` of this split).
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
variable {Ω : Type u} {N : Ω→ℕ} {j R B W C ρ : ℝ}
variable {J : ∀a,Interaction (N a)} {h e : ∀a,Fin (N a)→ℝ}

lemma gibbs_selected_all_directions_s2 (d : ℕ) (hρ : 0<ρ)
    (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 d 0) B W C (d+1) (2*d) (J a)) :
    ∃A:ℝ,0≤A ∧ ∀a (e:Fin (N a)→ℝ),vectorNorm e≤1→∀f:Observables (N a),
      |∑x,fieldGibbs (J a) (h a) x*(f x)^2*
        (∑k∈Finset.range (d-1),cutoffWeight (fun l=>residualCutoff ρ j (J a) (h a) l x) k*
          (∑i,(spin x i-mag j (J a) (h a) (k+2) x i)*e i))|≤
      A*starSquared (fieldGibbs (J a) (h a)) f := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end
