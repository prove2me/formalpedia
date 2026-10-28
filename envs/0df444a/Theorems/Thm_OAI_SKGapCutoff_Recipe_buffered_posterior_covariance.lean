-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_buffered_posterior_covariance
-- name    : OAI.SKGapCutoff.Recipe.buffered_posterior_covariance
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:26:23.337985+00:00
-- url     : https://prove2.me/theorems/1df4a5eb-ee05-46b0-b9b4-02da72df886a
-- title:
--   OAI.SKGapCutoff.Recipe.buffered_posterior_covariance: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGapCutoff.Recipe.buffered_posterior_covariance` of [lean/OAI/Probability/SKGap/Posterior/BufferedPosteriorCovariance.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Posterior/BufferedPosteriorCovariance.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators Matrix.Norms.Frobenius`, `open SKGap.Stein Primary Static`):
--
--   ```lean
--   theorem buffered_posterior_covariance {j K B Aroot ε c r₀ R ρ : ℝ}
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
--       : ∃A : ℕ→ℝ,(∀k,1≤A k) ∧ ∀m:ℕ,∀δ:ℝ,0<δ→
--         2<(m:ℝ)*ρ^2/4→2*(2*m:ℕ)*δ≤1→∀W C:ℝ,0≤W→0≤C→
--         ∀(Ω : Type u) (n : Ω→ℕ) (J : ∀b,Interaction (n b))
--         (h : ∀b,Fin (n b)→ℝ),
--         (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b i,J b i i=0)→
--         (∀b k,k<2*m-1→StartedMatrixEvent j K (Real.exp (R/2)) (A k) (c/2) B W C (k+3) (2+2*(k+1)) (J b))→
--         (∀b,RecipeMatrixEvent j K (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (J b))→
--         (∀b,¬SKGap.rootBad j Aroot ε c r₀ (J b) (h b))→
--         (∀b k,k<2*m-1→4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n b:ℝ))→
--         ∃D≥0,∀b (G : Observables (n b)),
--           vectorNorm (centeredSpinCovariance (fieldGibbs (J b) (h b)) G)≤
--             D*Real.sqrt ((∑x,fieldGibbs (J b) (h b) x*
--               (G x-∑y,fieldGibbs (J b) (h b) y*G y)^2)+
--               varianceEnergy (fieldGibbs (J b) (h b)) G)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.rootBad`, `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Observables`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.fieldGibbs`, `OAI.SKGapCutoff.Recipe.vectorNorm`, `OAI.SKGapCutoff.Static.centeredSpinCovariance`, `OAI.SKGapCutoff.Static.varianceEnergy`, `OAI.SKGap.Stein.KernelExpr` and `OAI.SKGap.Stein.KernelExpr.dr` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.RecipeMatrixEvent`, `OAI.SKGapCutoff.Recipe.StartedMatrixEvent`, `OAI.SKGapCutoff.Recipe.literalSizeBudget`, `OAI.SKGapCutoff.Recipe.residualCoefficientBudget` and `OAI.SKGapCutoff.Recipe.residualDerivativeBudget` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.FullMain.quenched_posterior_covariance` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Posterior/BufferedPosteriorCovariance.lean (declaration OAI.SKGapCutoff.Recipe.buffered_posterior_covariance)

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

theorem buffered_posterior_covariance {j K B Aroot ε c r₀ R ρ : ℝ}
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
    : ∃A : ℕ→ℝ,(∀k,1≤A k) ∧ ∀m:ℕ,∀δ:ℝ,0<δ→
      2<(m:ℝ)*ρ^2/4→2*(2*m:ℕ)*δ≤1→∀W C:ℝ,0≤W→0≤C→
      ∀(Ω : Type u) (n : Ω→ℕ) (J : ∀b,Interaction (n b))
      (h : ∀b,Fin (n b)→ℝ),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b i,J b i i=0)→
      (∀b k,k<2*m-1→StartedMatrixEvent j K (Real.exp (R/2)) (A k) (c/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b,RecipeMatrixEvent j K (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (J b))→
      (∀b,¬SKGap.rootBad j Aroot ε c r₀ (J b) (h b))→
      (∀b k,k<2*m-1→4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n b:ℝ))→
      ∃D≥0,∀b (G : Observables (n b)),
        vectorNorm (centeredSpinCovariance (fieldGibbs (J b) (h b)) G)≤
          D*Real.sqrt ((∑x,fieldGibbs (J b) (h b) x*
            (G x-∑y,fieldGibbs (J b) (h b) y*G y)^2)+
            varianceEnergy (fieldGibbs (J b) (h b)) G) := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end
