-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_hform_eq_entry
-- name    : GlobalTheory.CompanionTheory.SW.GramAlg.hform_eq_entry
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:05:48.920591+00:00
-- url     : https://prove2.me/theorems/b098191d-e891-44db-9ba5-1d5253753702
-- title:
--   Gram Alg: hform eq entry
-- statement:
--   The Gram Alg construction uses the hform eq entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightActionIdentities.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightActionIdentities.lean#L20-L25

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramAlg
variable {A : Type} [CommRing A] {M n : ℕ}

theorem GlobalTheory.CompanionTheory.SW.GramAlg.hform_eq_entry (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (X : Fin n → Fin M → A)
    (a b : Fin n) :
    hform s J (X a) (X b) = (cT s (colM X) * J * colM X) a b := by sorry
