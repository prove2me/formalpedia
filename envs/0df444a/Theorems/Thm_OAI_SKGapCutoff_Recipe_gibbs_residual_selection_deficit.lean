-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_gibbs_residual_selection_deficit
-- name    : OAI.SKGapCutoff.Recipe.gibbs_residual_selection_deficit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:28:06.454681+00:00
-- url     : https://prove2.me/theorems/0cee08df-13a1-4590-971b-ccfeb6c91035
-- title:
--   OAI.SKGapCutoff.Recipe.gibbs_residual_selection_deficit: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGapCutoff.Recipe.gibbs_residual_selection_deficit` of [lean/OAI/Probability/SKGap/Localization/SelectionDeficit.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/SelectionDeficit.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators`, `open Primary Static`):
--
--   ```lean
--   theorem gibbs_residual_selection_deficit (m : ℕ) (hρ : 0<ρ) (hε : 0<ε)
--       (hm : 2<(m:ℝ)*ρ^2/4) (he : 2*(2*m:ℕ)*ε≤1)
--       (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
--       (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
--       (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (J a)) :
--       ∃D≥0,∀a (r e : Fin (N a)→ℝ),vectorNorm e≤1→∀G : Observables (N a),
--         |∑x,fieldGibbs (J a) (h a) x*G x*
--           (cutoffDeficit (fun k=>residualCutoff ρ j (J a) (h a) k x) (2*m-1)*
--             (∑i,(spin x i-Real.tanh (r i))*e i))|≤D*starNorm (fieldGibbs (J a) (h a)) G
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Observables`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.fieldGibbs`, `OAI.SKGapCutoff.spin` and `OAI.SKGapCutoff.Recipe.vectorNorm` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.cutoffDeficit` (definitions bundle `OAIQ072A001` of this split); `OAI.SKGapCutoff.Recipe.RecipeMatrixEvent`, `OAI.SKGapCutoff.Recipe.residualCoefficientBudget`, `OAI.SKGapCutoff.Recipe.residualCutoff` and `OAI.SKGapCutoff.Static.starNorm` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** The proof of `OAI.SKGapCutoff.Recipe.buffered_posterior_covariance` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/SelectionDeficit.lean (declaration OAI.SKGapCutoff.Recipe.gibbs_residual_selection_deficit)

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
variable {n : ℕ}

universe u
variable {Ω : Type u} {N : Ω→ℕ} {j R B W C ρ ε : ℝ}
variable {J : ∀a,Interaction (N a)} {h : ∀a,Fin (N a)→ℝ}

theorem gibbs_residual_selection_deficit (m : ℕ) (hρ : 0<ρ) (hε : 0<ε)
    (hm : 2<(m:ℝ)*ρ^2/4) (he : 2*(2*m:ℕ)*ε≤1)
    (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (J a)) :
    ∃D≥0,∀a (r e : Fin (N a)→ℝ),vectorNorm e≤1→∀G : Observables (N a),
      |∑x,fieldGibbs (J a) (h a) x*G x*
        (cutoffDeficit (fun k=>residualCutoff ρ j (J a) (h a) k x) (2*m-1)*
          (∑i,(spin x i-Real.tanh (r i))*e i))|≤D*starNorm (fieldGibbs (J a) (h a)) G := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end
