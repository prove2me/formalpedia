-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_lt_of_blk_lt
-- name    : GlobalTheory.InertZeta.lt_of_blk_lt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:18:47.247564+00:00
-- url     : https://prove2.me/theorems/7bbed449-8da4-48e3-8460-a0052f3d55b2
-- title:
--   Inert Zeta: lt of blk lt
-- statement:
--   The Inert Zeta construction uses the lt of blk lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryIwasawaCosetSurjOfLeviElementExists.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryIwasawaCosetSurjOfLeviElementExists.lean#L18-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryIwasawaCosetSurjOfLeviElementExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta

theorem GlobalTheory.InertZeta.lt_of_blk_lt {N : ℕ} {a b : Fin (N + 2)} (h : blk N a < blk N b) : a < b := by sorry
