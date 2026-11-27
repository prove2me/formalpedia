-- Prove2me | Theorems.Thm_GlobalTheory_GenChar_ge_of_eigen
-- name    : GlobalTheory.GenChar.ge_of_eigen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:24:14.919208+00:00
-- url     : https://prove2.me/theorems/52f3d4bd-8d1c-5548-ba08-c85df6d93256
-- title:
--   Gen Char: ge of eigen
-- statement:
--   The Gen Char construction uses the ge of eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsIntegralCharacterGeneralizedEigen.lean#L40-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsIntegralCharacterGeneralizedEigen.lean#L40-L71

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCharacterGeneralizedEigen
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec

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
open GlobalTheory GlobalTheory.GenChar

theorem GlobalTheory.GenChar.ge_of_eigen {C : Type} [Field C] (V : VF C) {κ : Type} [Fintype κ]
    (A : Matrix κ κ C) (hA : ∀ i j, V.Ge 0 (A i j)) (c : C) (u : κ → C) (hu : u ≠ 0)
    (h : A.mulVec u = c • u) : V.Ge 0 c := by sorry
