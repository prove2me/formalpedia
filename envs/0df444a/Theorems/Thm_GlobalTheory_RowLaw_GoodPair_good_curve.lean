-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GoodPair_good_curve
-- name    : GlobalTheory.RowLaw.GoodPair.good_curve
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T06:06:38.559383+00:00
-- url     : https://prove2.me/theorems/9c83df3c-61e7-5a0a-b5e1-a98ac67c22a8
-- title:
--   Good Pair: good curve
-- statement:
--   The Good Pair construction uses the good curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodCurvesPairingMemMaxIdeal.lean#L660-L707
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodCurvesPairingMemMaxIdeal.lean#L660-L707

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusMemTypicalCurveSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodCurvesPairingMemMaxIdeal
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd GlobalTheory.RowVal MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GoodPair
variable {C : Type} [Field C]
variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}

theorem GlobalTheory.RowLaw.GoodPair.good_curve [NeZero d] {g : Fin 2} (H : X.CartHyp V g) {a : ZMod d} {w : I g → C}
    {x : ℕ → I g ⊕ JJ I g → C} (hx : (RawChart.cart H).Good a w x) :
    ∃ γ : κ → PowerSeries C, IsCv V γ ∧
      (∀ i n, V.l ∣ n → n < V.l * V.l → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0) ∧
      (∀ i, PowerSeries.coeff 1 (alongCv γ (X.lg i)) = ∑ c, X.u g c i * w c) ∧
      (∀ i, (V.l : C) * PowerSeries.coeff (V.l * V.l) (alongCv γ (X.lg i)) =
        ∑ c, X.u g c i * (RawChart.cart H).V2 x c) ∧
      ∀ q : I (1 - g), ∃ z, V.Ge 0 z ∧ (V.l : C) * PowerSeries.coeff V.l (alongCv γ (X.sg (X.u (1 - g) q))) =
        (V.l : C) * z - (RawChart.cart H).c0' x q := by sorry
