-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_literal_full_local_family_s2
-- name    : OAI.SKGapCutoff.Recipe.literal_full_local_family_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:52:46.406316+00:00
-- url     : https://prove2.me/theorems/3dfc2d47-ed7f-4d9e-99fc-00d14aa19972
-- title:
--   OAI.SKGapCutoff.Recipe.literal_full_local_family_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators`, `open Primary SKGap.Stein Static`):
--
--   ```lean
--   theorem literal_full_local_family_s2 (j : ℝ) (J : ∀b,Interaction (n b))
--       (h : ∀b,Fin (n b)→ℝ) (l : Fin M) (f : KernelExpr)
--       (a c : ∀b,Spin (n b)→ℝ) (r e : ∀b,Fin (n b)→ℝ)
--       (w y : ∀b,VectorFields (n b)) (E : ∀b,Set (Spin (n b)))
--       (hn : ∀b,0<n b) (he : ∀b,vectorNorm (e b)≤1)
--       {R B : ℝ} (hB : 0≤B)
--       (ha : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|a b x|≤R)
--       (hc : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|Real.sqrt (n b:ℝ)*c b x|≤B)
--       (heq : ∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) l.val)
--         (mag j (J b) (h b) l.val) (w b) (y b) (a b) (c b) (r b) (e b) x) :
--       LocalFamilyRecipe E j J h (fun b=>literalFullParameters j (J b) (h b) (a b) (c b)) w y
--         (fun b=>literalFullData j (J b) (h b) l f (a b) (c b) (r b) (e b)) 1 l.val
--         (literalCoefficientBudget f j R B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.VectorFields`, `OAI.SKGap.Stein.KernelExpr`, `OAI.SKGapCutoff.Primary.fld`, `OAI.SKGapCutoff.Primary.mag`, `OAI.SKGapCutoff.Recipe.LocalFamilyRecipe`, `OAI.SKGapCutoff.Recipe.vectorNorm` and `OAI.SKGapCutoff.Static.flipNeighborhood` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.LiteralEquations`, `OAI.SKGapCutoff.Recipe.literalCoefficientBudget`, `OAI.SKGapCutoff.Recipe.literalFullData` and `OAI.SKGapCutoff.Recipe.literalFullParameters` (definitions bundle `OAIQ072A002` of this split).
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
open Primary SKGap.Stein Static

variable {n M : ℕ}

universe u
variable {Ω : Type u} {n : Ω→ℕ}

theorem literal_full_local_family_s2 (j : ℝ) (J : ∀b,Interaction (n b))
    (h : ∀b,Fin (n b)→ℝ) (l : Fin M) (f : KernelExpr)
    (a c : ∀b,Spin (n b)→ℝ) (r e : ∀b,Fin (n b)→ℝ)
    (w y : ∀b,VectorFields (n b)) (E : ∀b,Set (Spin (n b)))
    (hn : ∀b,0<n b) (he : ∀b,vectorNorm (e b)≤1)
    {R B : ℝ} (hB : 0≤B)
    (ha : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|a b x|≤R)
    (hc : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|Real.sqrt (n b:ℝ)*c b x|≤B)
    (heq : ∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) l.val)
      (mag j (J b) (h b) l.val) (w b) (y b) (a b) (c b) (r b) (e b) x) :
    LocalFamilyRecipe E j J h (fun b=>literalFullParameters j (J b) (h b) (a b) (c b)) w y
      (fun b=>literalFullData j (J b) (h b) l f (a b) (c b) (r b) (e b)) 1 l.val
      (literalCoefficientBudget f j R B) := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end
