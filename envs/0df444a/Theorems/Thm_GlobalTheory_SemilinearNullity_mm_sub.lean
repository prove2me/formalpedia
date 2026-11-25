-- Prove2me | Theorems.Thm_GlobalTheory_SemilinearNullity_mm_sub
-- name    : GlobalTheory.SemilinearNullity.mm_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:53.0167+00:00
-- url     : https://prove2.me/theorems/cd4fa9c7-3861-4df0-ae8b-84f4c40d2e2c
-- title:
--   Semilinear Nullity: mm sub
-- statement:
--   The Semilinear Nullity construction uses the mm sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowerSemilinearRankNullityModMaxIdeal.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowerSemilinearRankNullityModMaxIdeal.lean#L20-L23

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

theorem GlobalTheory.SemilinearNullity.mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by sorry
