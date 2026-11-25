-- Prove2me | Theorems.Thm_GlobalTheory_ClosedResidueExt_Unram_dvr
-- name    : GlobalTheory.ClosedResidueExt.Unram.dvr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:58:34.263515+00:00
-- url     : https://prove2.me/theorems/cdaf9cb2-ea5b-5f2e-ae80-092f4faa1ae1
-- title:
--   Unram: dvr
-- statement:
--   The Unram construction uses the dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIntegralExtIsAlgClosedResidueField.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIntegralExtIsAlgClosedResidueField.lean#L55-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIntegralExtIsAlgClosedResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedResidueExt
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]

theorem GlobalTheory.ClosedResidueExt.Unram.dvr {π : W} {R : Subalgebra W Ω} (h : Unram π R)
    (h0 : algebraMap W Ω π ≠ 0) : IsDiscreteValuationRing R := by sorry
