-- Prove2me | Theorems.Thm_GlobalTheory_BK_Descent_plus_act_join
-- name    : GlobalTheory.BK.Descent.plus_act_join
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:08:23.376273+00:00
-- url     : https://prove2.me/theorems/4322706c-7d48-426f-a08a-461457560da3
-- title:
--   Descent: plus act join
-- statement:
--   The Descent construction uses the plus act join property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InstTameDescentExponentDataPadicThree.lean#L465-L467
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InstTameDescentExponentDataPadicThree.lean#L465-L467

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a]
open GlobalTheory.BK.Descent
variable {P : PhiMod O K l e a ι} (Δ : Descent P) (g : TameGal K l e a)

theorem GlobalTheory.BK.Descent.plus_act_join [NeZero e] {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))
    (hinv : y ∈ Δ.inv) (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    (Δ.plus hy hinv).act g (join v f) = join (Δ.act g v) (ringAct g f) := by sorry
