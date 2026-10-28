-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_literal_complete_diagnostics
-- name    : OAI.SKGapCutoff.Recipe.literal_complete_diagnostics
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:28:08.654349+00:00
-- url     : https://prove2.me/theorems/3e95330a-19f2-42f3-884b-85c1f28119b5
-- title:
--   OAI.SKGapCutoff.Recipe.literal_complete_diagnostics: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGapCutoff.Recipe.literal_complete_diagnostics` of [lean/OAI/Probability/SKGap/Localization/LiteralLocalWeak.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/LiteralLocalWeak.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators Matrix.Norms.Frobenius`, `open SKGap.Stein Primary`):
--
--   ```lean
--   theorem literal_complete_diagnostics (j R ρ δ T L Q E : ℝ) (f : KernelExpr)
--       (hj : 0≤j) (hδ : 0<δ) (hρ : 0≤ρ) (hT : 0≤T) (hQ : 0≤Q)
--       (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
--       ∃B≥0,∃S≥0,∃F≥0,∃Bc≥0,∃Vc≥0,∀n : ℕ,0<n→∀(J : Interaction n) (z m : VectorFields n)
--         (a : Spin n→ℝ) (r e : Fin n→ℝ),J.IsSymm→SKGap.opNorm J≤L→vectorNorm e≤1→
--         ∃w y : VectorFields n,∃c : Spin n→ℝ,
--           (∀x,LiteralStableAt J j z m a r R ρ δ x→LiteralEquations J j f z m w y a c r e x) ∧
--           (∀x,LiteralStableAt J j z m a r R ρ δ x→|Real.sqrt n*c x|≤Bc) ∧
--           (∀x,LiteralStableAt J j z m a r R ρ δ x→
--             (∀k,LiteralStableAt J j z m a r R ρ δ (flip x k))→
--             SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T→
--             SKGap.opNorm (derivativeMatrix m x)≤T→
--             ‖derivativeVector (fun v=>Real.sqrt n*c v) x‖≤Vc) ∧
--           (∀x (t : SKGap.Noncrossing.Primary.SourceTree (Fin n→ℝ)),
--             LiteralStableAt J j z m a r R ρ δ x→
--             (∀k,LiteralStableAt J j z m a r R ρ δ (flip x k))→
--             SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T→
--             SKGap.opNorm (derivativeMatrix m x)≤T→(∀i,|m x i|≤1)→
--             ‖derivativeMatrix z x-t.fieldMatrix j J‖≤E→
--             ‖derivativeMatrix m x-t.sourceMatrix j J‖≤E→
--             (∑i,∑k,(derivativeMatrix z x i k)^4)≤Q^4→
--             (∑i,(derivativeMatrix z x i i)^2)≤T^2→
--             LiteralInitialDiagnostics (literalInitial J j (Real.sqrt n) f z m a c r e)
--               w y t x B S F (Real.exp (R/2)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.opNorm`, `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.VectorFields`, `OAI.SKGapCutoff.flip`, `OAI.SKGap.Stein.KernelExpr`, `OAI.SKGapCutoff.Primary.derivativeMatrix`, `OAI.SKGapCutoff.Primary.derivativeVector`, `OAI.SKGapCutoff.Recipe.vectorNorm`, `OAI.SKGap.Noncrossing.Primary.SourceTree`, `OAI.SKGap.Noncrossing.Primary.SourceTree.fieldMatrix` and `OAI.SKGap.Noncrossing.Primary.SourceTree.sourceMatrix` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.LiteralEquations`, `OAI.SKGapCutoff.Recipe.LiteralInitialDiagnostics`, `OAI.SKGapCutoff.Recipe.LiteralStableAt` and `OAI.SKGapCutoff.Recipe.literalInitial` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** The proof of `OAI.SKGapCutoff.Recipe.buffered_root_source_weak` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/LiteralLocalWeak.lean (declaration OAI.SKGapCutoff.Recipe.literal_complete_diagnostics)

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
open SKGap.Stein Primary
variable {n : ℕ}

theorem literal_complete_diagnostics (j R ρ δ T L Q E : ℝ) (f : KernelExpr)
    (hj : 0≤j) (hδ : 0<δ) (hρ : 0≤ρ) (hT : 0≤T) (hQ : 0≤Q)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    ∃B≥0,∃S≥0,∃F≥0,∃Bc≥0,∃Vc≥0,∀n : ℕ,0<n→∀(J : Interaction n) (z m : VectorFields n)
      (a : Spin n→ℝ) (r e : Fin n→ℝ),J.IsSymm→SKGap.opNorm J≤L→vectorNorm e≤1→
      ∃w y : VectorFields n,∃c : Spin n→ℝ,
        (∀x,LiteralStableAt J j z m a r R ρ δ x→LiteralEquations J j f z m w y a c r e x) ∧
        (∀x,LiteralStableAt J j z m a r R ρ δ x→|Real.sqrt n*c x|≤Bc) ∧
        (∀x,LiteralStableAt J j z m a r R ρ δ x→
          (∀k,LiteralStableAt J j z m a r R ρ δ (flip x k))→
          SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T→
          SKGap.opNorm (derivativeMatrix m x)≤T→
          ‖derivativeVector (fun v=>Real.sqrt n*c v) x‖≤Vc) ∧
        (∀x (t : SKGap.Noncrossing.Primary.SourceTree (Fin n→ℝ)),
          LiteralStableAt J j z m a r R ρ δ x→
          (∀k,LiteralStableAt J j z m a r R ρ δ (flip x k))→
          SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T→
          SKGap.opNorm (derivativeMatrix m x)≤T→(∀i,|m x i|≤1)→
          ‖derivativeMatrix z x-t.fieldMatrix j J‖≤E→
          ‖derivativeMatrix m x-t.sourceMatrix j J‖≤E→
          (∑i,∑k,(derivativeMatrix z x i k)^4)≤Q^4→
          (∑i,(derivativeMatrix z x i i)^2)≤T^2→
          LiteralInitialDiagnostics (literalInitial J j (Real.sqrt n) f z m a c r e)
            w y t x B S F (Real.exp (R/2))) := by
  sorry
end SKGapCutoff.Recipe

end
end

end OAI
end
