-- Prove2me | Theorems.Thm_GlobalTheory_CongruentCharacters_pow_sub_pow_factor
-- name    : GlobalTheory.CongruentCharacters.pow_sub_pow_factor
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:11:57.275691+00:00
-- url     : https://prove2.me/theorems/03849844-1e7d-403d-99d1-cfb5923bb29e
-- title:
--   Congruent Characters: pow sub pow factor
-- statement:
--   The Congruent Characters construction uses the pow sub pow factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RingHomEqOfCongruentIntegralUnramified.lean#L39-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RingHomEqOfCongruentIntegralUnramified.lean#L39-L50

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RingHomEqOfCongruentIntegralUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.CongruentCharacters
variable {C : Type} [Field C] {V : VF C}

theorem GlobalTheory.CongruentCharacters.pow_sub_pow_factor {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (hab : V.MM (a - b)) (n : ℕ) :
    ∃ S : C, a ^ (n + 1) - b ^ (n + 1) = (a - b) * S ∧
      V.MM (S - ((n + 1 : ℕ) : C) * b ^ n) := by sorry
