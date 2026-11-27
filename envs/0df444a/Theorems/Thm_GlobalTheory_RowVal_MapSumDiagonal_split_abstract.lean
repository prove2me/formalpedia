-- Prove2me | Theorems.Thm_GlobalTheory_RowVal_MapSumDiagonal_split_abstract
-- name    : GlobalTheory.RowVal.MapSumDiagonal.split_abstract
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T06:15:08.161385+00:00
-- url     : https://prove2.me/theorems/3194c371-a6dd-45ff-aae0-590378e45da4
-- title:
--   Map Sum Diagonal: split abstract
-- statement:
--   The Map Sum Diagonal construction uses the split abstract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DiagonalSplit.lean#L27-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DiagonalSplit.lean#L27-L58

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeBiadditiveSymmAdjointIntegralEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DiagonalSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowVal GlobalTheory.RowVal.MapSumDiagonal

theorem GlobalTheory.RowVal.MapSumDiagonal.split_abstract {R Q Orb : Type} [Ring R] [AddCommGroup Q] [Fintype Orb] (P : R → Prop) (h : R → R → Q)
    (P0 : P 0) (Padd : ∀ a b, P a → P b → P (a + b)) (Pmul : ∀ a b, P a → P b → P (a * b))
    (h0 : ∀ a, h a 0 = 0 ∧ h 0 a = 0)
    (hl : ∀ a a' b, P a → P a' → P b → h (a + a') b = h a b + h a' b)
    (hr : ∀ a a' b, P a → P a' → P b → h b (a + a') = h b a + h b a')
    (hs : ∀ a b, P a → P b → h b a = h a b)
    (W W' : R) (hW : P W) (hW' : P W') (hadj : ∀ a b, P a → P b → h (W * a) b = h a (W' * b))
    (hWW : W + W' = 1) (π : Orb → Fin 2 → R) (hπ : ∀ o g, P (π o g))
    (horth : ∀ o g o' g', ¬ (o = o' ∧ g' = 1 - g) → h (π o g) (W * π o' g') = 0) :
    ∑ o, h (π o 0) (π o 1) = h (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) := by sorry
