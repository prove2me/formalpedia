-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_smul_tot_mem_Mext
-- name    : GlobalTheory.BK.PhiMod.smul_tot_mem_Mext
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:42:59.158174+00:00
-- url     : https://prove2.me/theorems/5f3ca9e8-16e8-400d-861f-0e1c01c3c8dd
-- title:
--   Phi Mod: smul tot mem Mext
-- statement:
--   The Phi Mod construction uses the smul tot mem Mext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L398-L400
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L398-L400

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
variable (P : PhiMod O K l e a ι)
omit [Fact l.Prime]

theorem GlobalTheory.BK.PhiMod.smul_tot_mem_Mext {B : Subalgebra O K⟦X⟧} {f : ZMod a → K⟦X⟧} (hf : ∀ τ, f τ ∈ B)
    {v : Vec K a ι} (hv : v ∈ P.Mext B) : f • v ∈ P.Mext B := by sorry
