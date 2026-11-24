-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SelfReciprocalLocalField_invol_algebraMap
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol_algebraMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:16:06.297593+00:00
-- url     : https://prove2.me/theorems/d85731f5-f50c-4f2b-accd-29879bf9daad
-- title:
--   Self Reciprocal Local Field: invol algebra Map
-- statement:
--   The Self Reciprocal Local Field construction uses the invol algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/SelfReciprocalLocalField.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/SelfReciprocalLocalField.lean#L97-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SelfReciprocalLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
variable {r : ℕ} (P : SelfRecip E r)

theorem GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol_algebraMap (e : E) :
    invol P (algebraMap E (Fld P) e) = algebraMap E (Fld P) (IsCMField.complexConj E e) := by sorry
