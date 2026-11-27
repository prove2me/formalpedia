-- Prove2me | Theorems.Thm_GlobalTheory_TeichSeq_frob_iter
-- name    : GlobalTheory.TeichSeq.frob_iter
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:17:02.021315+00:00
-- url     : https://prove2.me/theorems/173f77dd-1d71-4cc6-a92f-f91480ab8975
-- title:
--   Teich Seq: frob iter
-- statement:
--   The Teich Seq construction uses the frob iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FrobeniusLiftEmbeddingsUnit.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FrobeniusLiftEmbeddingsUnit.lean#L14-L19

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqOfMapEqOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusLiftEmbeddingsUnit
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
open GlobalTheory GlobalTheory.TeichSeq

theorem GlobalTheory.TeichSeq.frob_iter {O k : Type} [CommRing O] [CommRing k] {d : ℕ} (l : ℕ)
    (φ : ZMod d → (O →+* k)) (h : ∀ a x, φ (a + 1) x = φ a x ^ l) (a : ZMod d) (x : O) (n : ℕ) :
    φ (a + n) x = φ a x ^ l ^ n := by sorry
