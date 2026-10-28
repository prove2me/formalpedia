-- Prove2me | Theorems.Thm_OAI_SKGapCutoff_Recipe_primary_finite_control
-- name    : OAI.SKGapCutoff.Recipe.primary_finite_control
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:29:19.738462+00:00
-- url     : https://prove2.me/theorems/cbc8e3d9-a361-41df-9d6f-4bd13760ca26
-- title:
--   OAI.SKGapCutoff.Recipe.primary_finite_control: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGapCutoff.Recipe.primary_finite_control` of [lean/OAI/Probability/SKGap/Localization/PrimaryFiniteControl.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/PrimaryFiniteControl.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGapCutoff.Recipe`, with `open scoped BigOperators`, `open Primary Static SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial`):
--
--   ```lean
--   theorem primary_finite_control (j R B : ℝ) (hR : 0≤R) (hB : 0≤B)
--       (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ) (M Nmax : ℕ)
--       (hn : ∀a,0<n a) (hJ : ∀a,SKGap.opNorm (J a)≤R)
--       (hformal : ∀a x l,l<M → ShapeBound (formalField j (J a) (h a) x l) B)
--       (A W D : ℝ) (hA : 1≤A) (hW : 0≤W) (hD : 0≤D)
--       (hw : ∀a,WordTestBound (J a) A W (2*Nmax+3))
--       (hd : ∀a,WordDiagramBound (J a) j A D ((2*M+1)+2*Nmax+2)) :
--       FiniteRecipeControl j J h M Nmax A
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.opNorm`, `OAI.SKGapCutoff.Interaction`, `OAI.SKGapCutoff.Spin`, `OAI.SKGapCutoff.Primary.ShapeBound` and `OAI.SKGapCutoff.Primary.formalField` (definitions bundle `OAIQ072A000` of this split); `OAI.SKGapCutoff.Recipe.FiniteRecipeControl`, `OAI.SKGapCutoff.Recipe.WordDiagramBound` and `OAI.SKGapCutoff.Recipe.WordTestBound` (definitions bundle `OAIQ072A002` of this split).
--
--   **Used by.** The proofs of `OAI.SKGapCutoff.Recipe.buffered_posterior_covariance`, `OAI.SKGapCutoff.Recipe.gibbs_residual_selection_tail` and `OAI.SKGapCutoff.Recipe.uniform_stable_square_mean` of this split import it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Localization/PrimaryFiniteControl.lean (declaration OAI.SKGapCutoff.Recipe.primary_finite_control)

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
open Primary Static SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
universe u
variable {Ω : Type u} {n : Ω→ℕ}

theorem primary_finite_control (j R B : ℝ) (hR : 0≤R) (hB : 0≤B)
    (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ) (M Nmax : ℕ)
    (hn : ∀a,0<n a) (hJ : ∀a,SKGap.opNorm (J a)≤R)
    (hformal : ∀a x l,l<M → ShapeBound (formalField j (J a) (h a) x l) B)
    (A W D : ℝ) (hA : 1≤A) (hW : 0≤W) (hD : 0≤D)
    (hw : ∀a,WordTestBound (J a) A W (2*Nmax+3))
    (hd : ∀a,WordDiagramBound (J a) j A D ((2*M+1)+2*Nmax+2)) :
    FiniteRecipeControl j J h M Nmax A := by
  sorry

end SKGapCutoff.Recipe

end
end

end OAI
end
