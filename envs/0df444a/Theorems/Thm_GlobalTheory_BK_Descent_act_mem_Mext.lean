-- Prove2me | Theorems.Thm_GlobalTheory_BK_Descent_act_mem_Mext
-- name    : GlobalTheory.BK.Descent.act_mem_Mext
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:07:47.117876+00:00
-- url     : https://prove2.me/theorems/8f4ffbc9-d533-40be-9789-4f630e729fc2
-- title:
--   Descent: act mem Mext
-- statement:
--   The Descent construction uses the act mem Mext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InstTameDescentExponentDataPadicThree.lean#L373-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InstTameDescentExponentDataPadicThree.lean#L373-L379

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

theorem GlobalTheory.BK.Descent.act_mem_Mext {B : Subalgebra O K⟦X⟧} (hA : A O K ≤ B) (hB : Rot e B) {v : Vec K a ι}
    (hv : v ∈ P.Mext B) : Δ.act g v ∈ P.Mext B := by sorry
