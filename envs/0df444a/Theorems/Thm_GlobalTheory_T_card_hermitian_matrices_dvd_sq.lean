-- Prove2me | Theorems.Thm_GlobalTheory_T_card_hermitian_matrices_dvd_sq
-- name    : GlobalTheory.T.card_hermitian_matrices_dvd_sq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:46:53.728144+00:00
-- url     : https://prove2.me/theorems/4c367a33-ea05-5b72-afc2-b19f6edf15a5
-- title:
--   T: card hermitian matrices dvd sq
-- statement:
--   The T construction uses the card hermitian matrices dvd sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianMatricesDvdSqStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianMatricesDvdSqStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_hermitian_matrices_dvd_sq : ∀ {A : Type} [CommRing A] [Finite A] (c : A →+* A), (∀ u, c (c u) = u) → ∀ (ω : A), IsUnit (ω - c ω) → ∀ (p : A), c p = p → ∀ (m : ℕ), Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ^ 2 = Nat.card {u : A // p ∣ u} ^ (m * m) := by sorry
