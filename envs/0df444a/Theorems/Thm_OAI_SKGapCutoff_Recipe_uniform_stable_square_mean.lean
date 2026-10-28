-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_uniform_stable_square_mean
-- name    : OAI.SKGapCutoff.Recipe.uniform_stable_square_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:29:38.753992+00:00
-- url     : https://prove2.me/theorems/b5b58da3-e89d-43df-b435-8c4fb4862d4d
-- title:
--   OAI.SKGapCutoff.Recipe.uniform_stable_square_mean: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGapCutoff.Recipe.uniform_stable_square_mean` of [lean/OAI/Probability/SKGap/Entropy/NormalizedWeightedMean.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Entropy/NormalizedWeightedMean.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators`, `open Primary Static`):
--
--   ```lean
--   theorem uniform_stable_square_mean {j R B W C c r₀ ρ ε : ℝ} (m : ℕ)
--       (hj : 0≤j) (hR : 0≤R) (hc : 0 < c) (hr₀ : 0 < r₀) (hρ : 0<ρ) (hε : 0<ε)
--       (hbuffer : (R+4*j)*ρ < r₀) (hm : 2<(m:ℝ)*ρ^2/4) (he : 2*(2*m:ℕ)*ε≤1)
--       (hB : 0≤B) (hW : 0≤W) (hC : 0≤C) :
--       ∃A:ℝ,0≤A ∧ ∀{n:ℕ},0<n→∀(J:Interaction n) (h:Fin n→ℝ),
--         J.IsSymm→(∀i,J i i=0)→
--         RecipeMatrixEvent j R (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) J→
--         (∀y,vectorNorm (SKGap.tapField j J h y) ≤ r₀*Real.sqrt (n:ℝ)→∀v,
--           c*SKGap.vectorSqNorm v≤SKGap.quadraticForm (SKGap.fieldHessian j J y (SKGap.spinVariance y)) v)→
--         ∃r:Fin n→ℝ,SKGap.tapField j J h r=0 ∧ (∀y,SKGap.tapField j J h y=0→y=r) ∧
--           ∀f:Observables n,0<(∑x,fieldGibbs J h x*(f x)^2)→
--           vectorNorm (squareMean (fieldGibbs J h) f-SKGap.magnetization r)/Real.sqrt (n:ℝ)≤
--             ((1+(R+3*j)/c)*(R+4*j))*ρ+A/Real.sqrt (n:ℝ)*
--               (1+varianceEnergy (fieldGibbs J h) f/(∑x,fieldGibbs J h x*(f x)^2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.Field`, `OAI.SKGap.fieldHessian`, `OAI.SKGap.magnetization`, `OAI.SKGap.quadraticForm`, `OAI.SKGap.spinVariance`, `OAI.SKGap.tapField`, `OAI.SKGap.vectorSqNorm`, `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Observables`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.fieldGibbs`, `OAI.SKGapCutoff.Recipe.vectorNorm` and `OAI.SKGapCutoff.Static.varianceEnergy` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.RecipeMatrixEvent`, `OAI.SKGapCutoff.Recipe.residualCoefficientBudget` and `OAI.SKGapCutoff.Recipe.squareMean` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.sk_main` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Entropy/NormalizedWeightedMean.lean (declaration OAI.SKGapCutoff.Recipe.uniform_stable_square_mean)

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

theorem uniform_stable_square_mean {j R B W C c r₀ ρ ε : ℝ} (m : ℕ)
    (hj : 0≤j) (hR : 0≤R) (hc : 0 < c) (hr₀ : 0 < r₀) (hρ : 0<ρ) (hε : 0<ε)
    (hbuffer : (R+4*j)*ρ < r₀) (hm : 2<(m:ℝ)*ρ^2/4) (he : 2*(2*m:ℕ)*ε≤1)
    (hB : 0≤B) (hW : 0≤W) (hC : 0≤C) :
    ∃A:ℝ,0≤A ∧ ∀{n:ℕ},0<n→∀(J:Interaction n) (h:Fin n→ℝ),
      J.IsSymm→(∀i,J i i=0)→
      RecipeMatrixEvent j R (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) J→
      (∀y,vectorNorm (SKGap.tapField j J h y) ≤ r₀*Real.sqrt (n:ℝ)→∀v,
        c*SKGap.vectorSqNorm v≤SKGap.quadraticForm (SKGap.fieldHessian j J y (SKGap.spinVariance y)) v)→
      ∃r:Fin n→ℝ,SKGap.tapField j J h r=0 ∧ (∀y,SKGap.tapField j J h y=0→y=r) ∧
        ∀f:Observables n,0<(∑x,fieldGibbs J h x*(f x)^2)→
        vectorNorm (squareMean (fieldGibbs J h) f-SKGap.magnetization r)/Real.sqrt (n:ℝ)≤
          ((1+(R+3*j)/c)*(R+4*j))*ρ+A/Real.sqrt (n:ℝ)*
            (1+varianceEnergy (fieldGibbs J h) f/(∑x,fieldGibbs J h x*(f x)^2)) := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end
