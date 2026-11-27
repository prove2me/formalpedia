-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_good_pairing_mem_max
-- name    : GlobalTheory.RowLaw.good_pairing_mem_max
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-27T06:05:17.972914+00:00
-- url     : https://prove2.me/theorems/87dffcdf-84c4-4748-b24b-0d27e3fea2c5
-- title:
--   Row Law: good pairing mem max
-- statement:
--   The Row Law construction uses the good pairing mem max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodCurvesPairingMemMaxIdeal.lean#L720-L752
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodCurvesPairingMemMaxIdeal.lean#L720-L752

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
open GlobalTheory.RowLaw.GoodPair

theorem GlobalTheory.RowLaw.good_pairing_mem_max : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ (H : ∀ g, X.CartHyp V g) (g : Fin 2) (a a' : ZMod d) (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C) (w' : I (1 - g) → C) (x' : ℕ → I (1 - g) ⊕ JJ I (1 - g) → C), (RawChart.cart (H g)).Good a w x → (RawChart.cart (H (1 - g))).Good a' w' x' → (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) → V.MM (∑ q : I (1 - g), (RawChart.cart (H g)).c0' x q * w' q) := by sorry
