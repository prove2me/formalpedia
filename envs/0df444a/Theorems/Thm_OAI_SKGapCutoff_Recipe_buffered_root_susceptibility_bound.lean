-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_buffered_root_susceptibility_bound
-- name    : OAI.SKGapCutoff.Recipe.buffered_root_susceptibility_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:26:52.682318+00:00
-- url     : https://prove2.me/theorems/4b6ddeba-9628-40d6-a9da-2e43b80f47ce
-- title:
--   OAI.SKGapCutoff.Recipe.buffered_root_susceptibility_bound: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGapCutoff.Recipe.buffered_root_susceptibility_bound` of [lean/OAI/Probability/SKGap/Localization/LiteralValues.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/LiteralValues.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators Matrix.Norms.Frobenius`, `open SKGap.Stein Primary Static`):
--
--   ```lean
--   theorem buffered_root_susceptibility_bound {j K B Aroot ε c r₀ R ρ : ℝ}
--       (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hA : 1≤Aroot) (hc : 0 < c)
--       (hr₀ : 0 < r₀) (hρ : 0<ρ) (hε : 0≤ε) (hAR : Real.exp (R/2)≤Aroot)
--       (hbuffer : (K+4*j)*(2*ρ) < r₀)
--       (hR : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤R)
--       (hsmall : (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤ε)
--       (himplicit : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤
--         c/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
--       (habsorb : (|j| *|literalSizeBudget j c R K
--           (KernelExpr.dr (KernelExpr.atom 0 0 false))|)*
--         ((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤(1:ℝ)/2)
--       (k : ℕ) :
--       ∃A≥1,∀W C : ℝ,0≤W→0≤C→∀(Ω : Type u) (n : Ω→ℕ)
--         (J : ∀b,Interaction (n b)) (h : ∀b,Fin (n b)→ℝ) (P : ∀b,Observables (n b)),
--         (∀b,0<n b)→(∀b,(J b).IsSymm)→
--         (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (c/2) B W C (k+3) (2+2*(k+1)) (J b))→
--         (∀b,¬SKGap.rootBad j Aroot ε c r₀ (J b) (h b))→
--         (∀b,4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n b:ℝ))→
--         (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
--         (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
--         ∃r : ∀b,Fin (n b)→ℝ,(∀b,SKGap.tapField j (J b) (h b) (r b)=0 ∧
--             ∀v,SKGap.tapField j (J b) (h b) v=0→v=r b) ∧
--         ∃D≥0,∀b,
--           ∑x,P b x*(residualCutoff ρ j (J b) (h b) k x*
--             literalSusceptibility (fld j (J b) (h b) (k+1))
--               (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) x)^2≤D
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.Field`, `OAI.SKGap.overlap`, `OAI.SKGap.rootBad`, `OAI.SKGap.tapField`, `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Observables`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.Primary.fld`, `OAI.SKGapCutoff.Primary.mag`, `OAI.SKGapCutoff.Primary.onsager`, `OAI.SKGapCutoff.Static.conditionalMean`, `OAI.SKGap.Stein.KernelExpr` and `OAI.SKGap.Stein.KernelExpr.dr` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.StartedMatrixEvent`, `OAI.SKGapCutoff.Recipe.literalSizeBudget`, `OAI.SKGapCutoff.Recipe.literalSusceptibility`, `OAI.SKGapCutoff.Recipe.residualCutoff` and `OAI.SKGapCutoff.Recipe.residualDerivativeBudget` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** The proof of `OAI.SKGapCutoff.Recipe.buffered_root_direction_weak` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/LiteralValues.lean (declaration OAI.SKGapCutoff.Recipe.buffered_root_susceptibility_bound)

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

theorem buffered_root_susceptibility_bound {j K B Aroot ε c r₀ R ρ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hA : 1≤Aroot) (hc : 0 < c)
    (hr₀ : 0 < r₀) (hρ : 0<ρ) (hε : 0≤ε) (hAR : Real.exp (R/2)≤Aroot)
    (hbuffer : (K+4*j)*(2*ρ) < r₀)
    (hR : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤R)
    (hsmall : (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤ε)
    (himplicit : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤
      c/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (habsorb : (|j| *|literalSizeBudget j c R K
        (KernelExpr.dr (KernelExpr.atom 0 0 false))|)*
      ((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤(1:ℝ)/2)
    (k : ℕ) :
    ∃A≥1,∀W C : ℝ,0≤W→0≤C→∀(Ω : Type u) (n : Ω→ℕ)
      (J : ∀b,Interaction (n b)) (h : ∀b,Fin (n b)→ℝ) (P : ∀b,Observables (n b)),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→
      (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (c/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b,¬SKGap.rootBad j Aroot ε c r₀ (J b) (h b))→
      (∀b,4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n b:ℝ))→
      (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
      (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
      ∃r : ∀b,Fin (n b)→ℝ,(∀b,SKGap.tapField j (J b) (h b) (r b)=0 ∧
          ∀v,SKGap.tapField j (J b) (h b) v=0→v=r b) ∧
      ∃D≥0,∀b,
        ∑x,P b x*(residualCutoff ρ j (J b) (h b) k x*
          literalSusceptibility (fld j (J b) (h b) (k+1))
            (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) x)^2≤D := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end
