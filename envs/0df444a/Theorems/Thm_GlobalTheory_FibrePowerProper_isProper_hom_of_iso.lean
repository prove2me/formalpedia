-- Prove2me | Theorems.Thm_GlobalTheory_FibrePowerProper_isProper_hom_of_iso
-- name    : GlobalTheory.FibrePowerProper.isProper_hom_of_iso
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:36.149312+00:00
-- url     : https://prove2.me/theorems/280ee8ef-437b-4dde-9fab-4a1ae9fa4611
-- title:
--   Fibre Power Proper: is Proper hom of iso
-- statement:
--   The Fibre Power Proper construction uses the is Proper hom of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperEighthFibrePowerOver.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperEighthFibrePowerOver.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperEighthFibrePowerOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FibrePowerProper

theorem GlobalTheory.FibrePowerProper.isProper_hom_of_iso {T : Scheme.{0}} {X Y : Over T} (e : X ≅ Y) (h : IsProper Y.hom) :
    IsProper X.hom := by sorry
