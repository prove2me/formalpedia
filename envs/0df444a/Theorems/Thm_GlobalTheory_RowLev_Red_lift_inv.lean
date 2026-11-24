-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_Red_lift_inv
-- name    : GlobalTheory.RowLev.Red.lift_inv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:28:42.232315+00:00
-- url     : https://prove2.me/theorems/8c7abbb2-ba99-47f3-b365-218cea755f37
-- title:
--   Red: lift inv
-- statement:
--   The Red construction uses the lift inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L183-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L183-L190

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

theorem GlobalTheory.RowLev.Red.lift_inv (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) (ha : IsSA a) (x : I.Gf) :
    ρ.lift μf a x⁻¹ = star (ρ.lift μf a x) := by sorry
