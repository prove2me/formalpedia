-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_literal_implicit_construction
-- name    : OAI.SKGapCutoff.Recipe.literal_implicit_construction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:29:19.399689+00:00
-- url     : https://prove2.me/theorems/d69a810a-f159-4ab6-bb13-defee48c73a1
-- title:
--   OAI.SKGapCutoff.Recipe.literal_implicit_construction: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGapCutoff.Recipe.literal_implicit_construction` of [lean/OAI/Probability/SKGap/Localization/LiteralConstruction.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/LiteralConstruction.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators Matrix.Norms.Frobenius`, `open SKGap.Stein Primary SKGap.ImplicitSystem Matrix`):
--
--   ```lean
--   theorem literal_implicit_construction (j R ρ δ T L : ℝ) (f : KernelExpr)
--       (hδ : 0<δ) (hρ : 0≤ρ) (hT : 0≤T)
--       (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
--       ∃C≥0,∀n : ℕ,0<n→∀(J : Interaction n) (z m : VectorFields n)
--         (a : Spin n→ℝ) (r e : Fin n→ℝ),SKGap.opNorm J≤L→vectorNorm e≤1→
--         ∃w y : VectorFields n,∃c : Spin n→ℝ,
--           (∀x,LiteralStableAt J j z m a r R ρ δ x→LiteralEquations J j f z m w y a c r e x) ∧
--           (∀x,LiteralStableAt J j z m a r R ρ δ x→
--             (∀k,LiteralStableAt J j z m a r R ρ δ (flip x k))→
--             SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T→
--             SKGap.opNorm (derivativeMatrix m x)≤T→
--             SmallBound w x C ∧ SmallBound y x C ∧ |Real.sqrt n*c x|≤C ∧
--               ‖derivativeVector (fun v=>Real.sqrt n*c v) x‖≤C)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.opNorm`, `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.VectorFields`, `OAI.SKGapCutoff.flip`, `OAI.SKGap.Stein.KernelExpr`, `OAI.SKGapCutoff.Primary.derivativeMatrix`, `OAI.SKGapCutoff.Primary.derivativeVector`, `OAI.SKGapCutoff.Recipe.SmallBound` and `OAI.SKGapCutoff.Recipe.vectorNorm` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.LiteralEquations` and `OAI.SKGapCutoff.Recipe.LiteralStableAt` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** The proof of `OAI.SKGapCutoff.Recipe.literal_complete_diagnostics` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/LiteralConstruction.lean (declaration OAI.SKGapCutoff.Recipe.literal_implicit_construction)

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
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

theorem literal_implicit_construction (j R ρ δ T L : ℝ) (f : KernelExpr)
    (hδ : 0<δ) (hρ : 0≤ρ) (hT : 0≤T)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    ∃C≥0,∀n : ℕ,0<n→∀(J : Interaction n) (z m : VectorFields n)
      (a : Spin n→ℝ) (r e : Fin n→ℝ),SKGap.opNorm J≤L→vectorNorm e≤1→
      ∃w y : VectorFields n,∃c : Spin n→ℝ,
        (∀x,LiteralStableAt J j z m a r R ρ δ x→LiteralEquations J j f z m w y a c r e x) ∧
        (∀x,LiteralStableAt J j z m a r R ρ δ x→
          (∀k,LiteralStableAt J j z m a r R ρ δ (flip x k))→
          SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T→
          SKGap.opNorm (derivativeMatrix m x)≤T→
          SmallBound w x C ∧ SmallBound y x C ∧ |Real.sqrt n*c x|≤C ∧
            ‖derivativeVector (fun v=>Real.sqrt n*c v) x‖≤C) := by
  sorry
end SKGapCutoff.Recipe

end
end

end OAI
end
