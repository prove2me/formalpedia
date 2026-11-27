-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_ge_zero_sg1_of_ty_ne
-- name    : GlobalTheory.RowLaw.ge_zero_sg1_of_ty_ne
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-27T05:11:40.524872+00:00
-- url     : https://prove2.me/theorems/6ca13918-3d90-5704-962b-27a1949751a8
-- title:
--   Row Law: ge zero sg1 of ty ne
-- statement:
--   The Row Law construction uses the ge zero sg1 of ty ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGaugeBilinearTermOfTypeNe.lean#L339-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGaugeBilinearTermOfTypeNe.lean#L339-L377

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGaugeBilinearTermOfTypeNe
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
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
variable {Y : RawChart C d I κ} {V : VF C}

theorem GlobalTheory.RowLaw.ge_zero_sg1_of_ty_ne (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type)
    [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ) (h : RLaw X V) (g : Fin 2)
    (hT : HasTeich X V g) (c : I g) (q : JJ I g) (hne : X.ty g c ≠ X.ty (1 - g) q) :
    V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q)) := by sorry
