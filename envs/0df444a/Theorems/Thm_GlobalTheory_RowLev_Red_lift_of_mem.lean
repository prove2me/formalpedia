-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_Red_lift_of_mem
-- name    : GlobalTheory.RowLev.Red.lift_of_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:41:16.035094+00:00
-- url     : https://prove2.me/theorems/74771a8a-dc99-4ce2-b0aa-825d69fa44a1
-- title:
--   Red: lift of mem
-- statement:
--   The Red construction uses the lift of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L160-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L160-L163

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
open Inhab
open GlobalTheory.RowLev.Red
variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)

theorem GlobalTheory.RowLev.Red.lift_of_mem (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) {x : I.Gf} (hx : x ∈ I.Kset) :
    ρ.lift μf a x = a.coeff (ρ.toFun x) / ((μf (I.Kg g)).toReal : ℂ) := by sorry
