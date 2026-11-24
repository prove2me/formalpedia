-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_prep_fixed
-- name    : GlobalTheory.PMonE.prep_fixed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:39:43.478308+00:00
-- url     : https://prove2.me/theorems/7a159bd6-1ba8-4b5b-876d-be62a5864fb2
-- title:
--   PMon E: prep fixed
-- statement:
--   The PMon E construction uses the prep fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L99-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L99-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type} [NormedField F] {m : Type} [Fintype m]
variable [IsUltrametricDist F]

theorem GlobalTheory.PMonE.prep_fixed [CompleteSpace F] {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) (M0 : Matrix m m F) (h0 : PrepBd 1 M0)
    (W : Matrix m m F → Matrix m m F) (hW : ∀ A, PrepBd 1 A → PrepBd δ (W A))
    (hW2 : ∀ A B ε, 0 ≤ ε → PrepBd 1 A → PrepBd 1 B → PrepBd ε (A - B) → PrepBd (δ * ε) (W A - W B)) :
    ∃ A, PrepBd 1 A ∧ A = -M0 - W A * A := by sorry
