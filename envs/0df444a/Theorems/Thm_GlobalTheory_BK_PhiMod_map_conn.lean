-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_map_conn
-- name    : GlobalTheory.BK.PhiMod.map_conn
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:43:00.927245+00:00
-- url     : https://prove2.me/theorems/a9b41716-3f5a-4752-9182-6f6075c1e2fc
-- title:
--   Phi Mod: map conn
-- statement:
--   The Phi Mod construction uses the map conn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L359-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L359-L368

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
variable {P}

theorem GlobalTheory.BK.PhiMod.map_conn {Q : PhiMod O K l e a κ} (g : Vec K a ι →+ Vec K a κ)
    (σ : (ZMod a → K⟦X⟧) → ZMod a → K⟦X⟧) (hσ : ∀ f, σ (NTot f) = NTot (σ f))
    (hs : ∀ f v, g (f • v) = σ f • g v) (hg : ∀ v, g (P.phi v) = Q.phi (g v)) (v : Vec K a ι) :
    g (P.conn v) = Q.conn (g v) := by sorry
