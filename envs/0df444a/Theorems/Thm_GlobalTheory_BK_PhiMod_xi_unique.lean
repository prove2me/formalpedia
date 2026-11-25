-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_xi_unique
-- name    : GlobalTheory.BK.PhiMod.xi_unique
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:55:37.493161+00:00
-- url     : https://prove2.me/theorems/f966b5cb-2201-5a5e-b2bf-abe72a0501c3
-- title:
--   Phi Mod: xi unique
-- statement:
--   The Phi Mod construction uses the xi unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L294-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L294-L300

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

theorem GlobalTheory.BK.PhiMod.xi_unique {s : P.D → Vec K a ι} (h0 : ∀ d, red (s d) = d)
    (h : ∀ d, P.phi (s d) = s (P.phiD d)) (d : P.D) : s d = P.xi d := by sorry
