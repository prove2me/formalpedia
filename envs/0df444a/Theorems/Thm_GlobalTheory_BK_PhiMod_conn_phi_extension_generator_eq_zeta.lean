-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_conn_phi_extension_generator_eq_zeta
-- name    : GlobalTheory.BK.PhiMod.conn_phi_extension_generator_eq_zeta
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:42:35.132215+00:00
-- url     : https://prove2.me/theorems/c1f010a2-9900-436d-bd9e-c5feac3ed02e
-- title:
--   Phi Mod: conn phi extension generator eq zeta
-- statement:
--   The Phi Mod construction uses the conn phi extension generator eq zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L551-L552
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L551-L552

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
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
  [Fact l.Prime]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι) {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))

theorem GlobalTheory.BK.PhiMod.conn_phi_extension_generator_eq_zeta : (P.plus hy).conn ((P.plus hy).phi xVec) = (P.plusInl hy).app (P.zeta y) := by sorry
