-- Prove2me | Theorems.Thm_GlobalTheory_SW_Vac_ex_two_eq_one
-- name    : GlobalTheory.SW.Vac.ex_two_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:41:40.06934+00:00
-- url     : https://prove2.me/theorems/9fedb456-374a-4b78-96c3-3eebe089f4c5
-- title:
--   Vac: ex two eq one
-- statement:
--   The Vac construction uses the ex two eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L62-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.Vac.ex_two_eq_one {r : ℚ} (h : ex (2 * r) = 1) : ∃ m : ℤ, r = m := by sorry
