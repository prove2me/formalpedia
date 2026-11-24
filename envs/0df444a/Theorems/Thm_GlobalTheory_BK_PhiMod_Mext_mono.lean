-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_Mext_mono
-- name    : GlobalTheory.BK.PhiMod.Mext_mono
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:43:10.645481+00:00
-- url     : https://prove2.me/theorems/4157d3fc-5157-41e3-a288-d6aeff5fc799
-- title:
--   Phi Mod: Mext mono
-- statement:
--   The Phi Mod construction uses the Mext mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L408-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L408-L409

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

theorem GlobalTheory.BK.PhiMod.Mext_mono {B B' : Subalgebra O K⟦X⟧} (h : B ≤ B') {v : Vec K a ι} (hv : v ∈ P.Mext B) :
    v ∈ P.Mext B' := by sorry
