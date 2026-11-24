-- Prove2me | Theorems.Thm_GlobalTheory_localizationAway_eq_zero_of_forall_eval
-- name    : GlobalTheory.localizationAway_eq_zero_of_forall_eval
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:59.598801+00:00
-- url     : https://prove2.me/theorems/f3c41a3f-28db-4654-b176-309734ee8483
-- title:
--   Global Theory: localization Away eq zero of forall eval
-- statement:
--   The Global Theory construction uses the localization Away eq zero of forall eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAlgHomLocalizationAwayOfRationalPoints.lean#L7-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAlgHomLocalizationAwayOfRationalPoints.lean#L7-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAlgHomLocalizationAwayOfRationalPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial

theorem GlobalTheory.localizationAway_eq_zero_of_forall_eval {k : Type} [Field k] [Infinite k]
    (D : Polynomial k) (hD : D ≠ 0) (b : Localization.Away D)
    (h : ∀ t, D.eval t ≠ 0 → ∀ e : Localization.Away D →+* k,
      (∀ q, e (algebraMap (Polynomial k) _ q) = q.eval t) → e b = 0) : b = 0 := by sorry
