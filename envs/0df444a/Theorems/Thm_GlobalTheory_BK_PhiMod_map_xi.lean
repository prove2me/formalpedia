-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_map_xi
-- name    : GlobalTheory.BK.PhiMod.map_xi
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:42:43.697799+00:00
-- url     : https://prove2.me/theorems/ba4106e7-5eb6-4b57-906b-53e94599af7c
-- title:
--   Phi Mod: map xi
-- statement:
--   The Phi Mod construction uses the map xi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L286-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L286-L292

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

theorem GlobalTheory.BK.PhiMod.map_xi {Q : PhiMod O K l e a κ} {g : Vec K a ι → Vec K a κ}
    (hg : ∀ v, g (P.phi v) = Q.phi (g v)) (d : P.D) : g (P.xi d) = Q.xi (red (g (P.xi d))) := by sorry
