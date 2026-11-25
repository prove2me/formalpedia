-- Prove2me | Theorems.Thm_GlobalTheory_SemilinearNullity_mm_int_mul
-- name    : GlobalTheory.SemilinearNullity.mm_int_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:53.882471+00:00
-- url     : https://prove2.me/theorems/a71c28e8-bbff-4781-8a3c-516f6a7d91ae
-- title:
--   Semilinear Nullity: mm int mul
-- statement:
--   The Semilinear Nullity construction uses the mm int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowerSemilinearRankNullityModMaxIdeal.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowerSemilinearRankNullityModMaxIdeal.lean#L15-L18

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSemilinearRankNullityModMaxIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.SemilinearNullity
variable {C : Type} [Field C] {V : VF C}

theorem GlobalTheory.SemilinearNullity.mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by sorry
