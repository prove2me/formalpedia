-- Prove2me | Theorems.Thm_GlobalTheory_SemilinearNullity_ge_inv
-- name    : GlobalTheory.SemilinearNullity.ge_inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:53.450921+00:00
-- url     : https://prove2.me/theorems/b222c287-971a-4963-938e-84ca6c236204
-- title:
--   Semilinear Nullity: ge inv
-- statement:
--   The Semilinear Nullity construction uses the ge inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowerSemilinearRankNullityModMaxIdeal.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowerSemilinearRankNullityModMaxIdeal.lean#L32-L38

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

theorem GlobalTheory.SemilinearNullity.ge_inv {a : C} (h : ¬ V.MM a) : V.Ge 0 a⁻¹ := by sorry
