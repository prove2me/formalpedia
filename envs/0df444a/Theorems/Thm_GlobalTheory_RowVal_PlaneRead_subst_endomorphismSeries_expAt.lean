-- Prove2me | Theorems.Thm_GlobalTheory_RowVal_PlaneRead_subst_endomorphismSeries_expAt
-- name    : GlobalTheory.RowVal.PlaneRead.subst_endomorphismSeries_expAt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-27T06:19:00.723576+00:00
-- url     : https://prove2.me/theorems/f98d6a55-2905-4bff-a49d-817c8f6fbceb
-- title:
--   Plane Read: subst endomorphism Series exp At
-- statement:
--   The Plane Read construction uses the subst endomorphism Series exp At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsIntegralSeriesFrameEqProdRows.lean#L37-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsIntegralSeriesFrameEqProdRows.lean#L37-L50

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeBiadditiveSymmAdjointIntegralEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralSeriesFrameEqProdRows
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowVal GlobalTheory.RowVal.PlaneRead
open MvPowerSeries EndCalc
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  {X : RawChart C d I κ}

theorem GlobalTheory.RowVal.PlaneRead.subst_endomorphismSeries_expAt (H : RLaw X V) {ω : Type} [Fintype ω] (v : ω → κ → C) (A : Matrix κ κ C) (i : κ) :
    subst (expAt X v) (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) i) =
      expAt X (fun w => A.mulVec (v w)) i := by sorry
