-- Prove2me | Theorems.Thm_GlobalTheory_SW_IpPos_intM_natCast_smul
-- name    : GlobalTheory.SW.IpPos.intM_natCast_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:18:05.027021+00:00
-- url     : https://prove2.me/theorems/a3e49056-a980-4ccd-89d0-efe54672d5f8
-- title:
--   Ip Pos: int M nat Cast smul
-- statement:
--   The Ip Pos construction uses the int M nat Cast smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInnerProductSelfNonnegBounds.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInnerProductSelfNonnegBounds.lean#L43-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBounds
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.IpPos
open NumberField
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
open Matrix Complex
open scoped ComplexConjugate Real
open NumberField
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
omit [NumberField K] [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.IpPos.intM_natCast_smul (n : ℕ) {x : Matrix κ ι K}
    (hx : _root_.GlobalTheory.SW.IntM x) : _root_.GlobalTheory.SW.IntM ((n : K) • x) := by sorry
