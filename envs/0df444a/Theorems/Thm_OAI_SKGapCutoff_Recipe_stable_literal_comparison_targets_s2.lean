-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_stable_literal_comparison_targets_s2
-- name    : OAI.SKGapCutoff.Recipe.stable_literal_comparison_targets_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:53:13.240539+00:00
-- url     : https://prove2.me/theorems/f798c323-897b-448e-9f5e-db6fcf8ffb7c
-- title:
--   OAI.SKGapCutoff.Recipe.stable_literal_comparison_targets_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators Matrix.Norms.Frobenius`, `open SKGap.Stein Primary Static`):
--
--   ```lean
--   theorem stable_literal_comparison_targets_s2 {j K B R ρ δ : ℝ}
--       (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hδ : 0<δ) (hρ : 0≤ρ)
--       (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
--       (k : ℕ) (f : KernelExpr) :
--       ∃A≥1,∀W C : ℝ,0≤W→0≤C→∀(Ω : Type u) (n : Ω→ℕ)
--         (J : ∀b,Interaction (n b)) (h r e : ∀b,Fin (n b)→ℝ)
--         (E : ∀b,Set (Spin (n b))) (P : ∀b,Observables (n b)),
--         (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b,vectorNorm (e b)≤1)→
--         (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (δ/2) B W C (k+3) (2+2*(k+1)) (J b))→
--         (∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→
--           LiteralStableAt (J b) j (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1))
--             (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) R ρ δ x)→
--         (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
--         (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
--         ∃w y : ∀b,VectorFields (n b),∃c : ∀b,Observables (n b),
--           (∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) (k+1))
--             (mag j (J b) (h b) (k+1)) (w b) (y b)
--             (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (c b) (r b) (e b) x) ∧
--           ((∀p≤k+1,LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) p x i*w b x i)) ∧
--           LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) (k+1) x i*y b x i) ∧
--           LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) (k+1) x i*
--             (Real.tanh (fld j (J b) (h b) (k+1) x i)/Real.sqrt (n b:ℝ))) ∧
--           LocalUniformMultiplier E (fun b=>siteMean (fun x i=>phi (fld j (J b) (h b) (k+1) x i) (r b i)
--             (j*(1-onsager j (J b) (h b) (k+1) x-SKGap.overlap (r b))))) ∧
--           LocalUniformMultiplier E (fun b x=>j*onsager j (J b) (h b) (k+1) x) ∧
--           LocalUniformMultiplier E (fun b x=>Real.sqrt (n b:ℝ)*c b x)) ∧
--           LocalUniformWeak E P (fun b x=>j*c b x*(∑i,residual j (J b) (h b) (k+1) x i*
--             (Real.tanh (fld j (J b) (h b) (k+1) x i)-Real.tanh (r b i))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.overlap`, `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Observables`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.VectorFields`, `OAI.SKGap.Stein.KernelExpr`, `OAI.SKGap.Stein.phi`, `OAI.SKGapCutoff.Primary.fld`, `OAI.SKGapCutoff.Primary.mag`, `OAI.SKGapCutoff.Primary.onsager`, `OAI.SKGapCutoff.Primary.residual`, `OAI.SKGapCutoff.Primary.siteMean`, `OAI.SKGapCutoff.Recipe.vectorNorm`, `OAI.SKGapCutoff.Static.LocalUniformMultiplier`, `OAI.SKGapCutoff.Static.conditionalMean` and `OAI.SKGapCutoff.Static.flipNeighborhood` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.LiteralEquations`, `OAI.SKGapCutoff.Recipe.LiteralStableAt`, `OAI.SKGapCutoff.Recipe.StartedMatrixEvent` and `OAI.SKGapCutoff.Static.LocalUniformWeak` (definitions bundle `OAIQ072A002` of this split).
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
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u
theorem stable_literal_comparison_targets_s2 {j K B R ρ δ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (k : ℕ) (f : KernelExpr) :
    ∃A≥1,∀W C : ℝ,0≤W→0≤C→∀(Ω : Type u) (n : Ω→ℕ)
      (J : ∀b,Interaction (n b)) (h r e : ∀b,Fin (n b)→ℝ)
      (E : ∀b,Set (Spin (n b))) (P : ∀b,Observables (n b)),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b,vectorNorm (e b)≤1)→
      (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (δ/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→
        LiteralStableAt (J b) j (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1))
          (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) R ρ δ x)→
      (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
      (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
      ∃w y : ∀b,VectorFields (n b),∃c : ∀b,Observables (n b),
        (∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) (k+1))
          (mag j (J b) (h b) (k+1)) (w b) (y b)
          (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (c b) (r b) (e b) x) ∧
        ((∀p≤k+1,LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) p x i*w b x i)) ∧
        LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) (k+1) x i*y b x i) ∧
        LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) (k+1) x i*
          (Real.tanh (fld j (J b) (h b) (k+1) x i)/Real.sqrt (n b:ℝ))) ∧
        LocalUniformMultiplier E (fun b=>siteMean (fun x i=>phi (fld j (J b) (h b) (k+1) x i) (r b i)
          (j*(1-onsager j (J b) (h b) (k+1) x-SKGap.overlap (r b))))) ∧
        LocalUniformMultiplier E (fun b x=>j*onsager j (J b) (h b) (k+1) x) ∧
        LocalUniformMultiplier E (fun b x=>Real.sqrt (n b:ℝ)*c b x)) ∧
        LocalUniformWeak E P (fun b x=>j*c b x*(∑i,residual j (J b) (h b) (k+1) x i*
          (Real.tanh (fld j (J b) (h b) (k+1) x i)-Real.tanh (r b i)))) := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end
