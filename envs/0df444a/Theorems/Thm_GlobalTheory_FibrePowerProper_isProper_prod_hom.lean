-- Prove2me | Theorems.Thm_GlobalTheory_FibrePowerProper_isProper_prod_hom
-- name    : GlobalTheory.FibrePowerProper.isProper_prod_hom
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:27.478395+00:00
-- url     : https://prove2.me/theorems/25f070af-1399-43d5-bdf2-575424c69470
-- title:
--   Fibre Power Proper: is Proper prod hom
-- statement:
--   The Fibre Power Proper construction uses the is Proper prod hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperEighthFibrePowerOver.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperEighthFibrePowerOver.lean#L13-L20

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

theorem GlobalTheory.FibrePowerProper.isProper_prod_hom {T : Scheme.{0}} (X Y : Over T) (hX : IsProper X.hom)
    (hY : IsProper Y.hom) : IsProper (X ⨯ Y).hom := by sorry
