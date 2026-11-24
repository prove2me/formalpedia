-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_auxiliary_places
-- name    : GlobalTheory.QNorm.exists_auxiliary_places
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:32:32.234844+00:00
-- url     : https://prove2.me/theorems/612cdf12-aeb6-4ad2-8cbc-59addbcef707
-- title:
--   QNorm: exists auxiliary places
-- statement:
--   The QNorm construction uses the exists auxiliary places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsAuxiliaryPlacesSquarePatternsSUnits.lean#L153-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsAuxiliaryPlacesSquarePatternsSUnits.lean#L153-L257

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPlaceIsSquareAndNotIsSquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAuxiliaryPlacesSquarePatternsSUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero

theorem GlobalTheory.QNorm.exists_auxiliary_places : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), _root_.GlobalTheory.QNorm.admitted F S → δ ∈ _root_.GlobalTheory.QNorm.sUnits F S → ¬ IsSquare (δ : F) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), Disjoint S T ∧ T.card + 1 = S.card + Fintype.card (InfinitePlace F) ∧ (∀ v ∈ T, IsSquare (algebraMap F (v.adicCompletion F) δ)) ∧ ∀ A : Finset (HeightOneSpectrum (𝓞 F)), ∃ u ∈ _root_.GlobalTheory.QNorm.sUnits F S, ∀ v ∈ T, (IsSquare (algebraMap F (v.adicCompletion F) u) ↔ v ∉ A) := by sorry
