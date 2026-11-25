-- Prove2me | Theorems.Thm_GlobalTheory_SemilinearNullity_ge_of_pow
-- name    : GlobalTheory.SemilinearNullity.ge_of_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:50.8454+00:00
-- url     : https://prove2.me/theorems/52e80f7c-f465-424e-a040-93fcad0a7b9b
-- title:
--   Semilinear Nullity: ge of pow
-- statement:
--   The Semilinear Nullity construction uses the ge of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowerSemilinearRankNullityModMaxIdeal.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowerSemilinearRankNullityModMaxIdeal.lean#L25-L30

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

theorem GlobalTheory.SemilinearNullity.ge_of_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (a ^ n)) : V.Ge 0 a := by sorry
