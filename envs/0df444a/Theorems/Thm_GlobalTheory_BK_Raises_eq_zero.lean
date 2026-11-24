-- Prove2me | Theorems.Thm_GlobalTheory_BK_Raises_eq_zero
-- name    : GlobalTheory.BK.Raises.eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:42:57.51503+00:00
-- url     : https://prove2.me/theorems/ef029ae6-86d9-487e-8591-852f31e4ed9b
-- title:
--   Raises: eq zero
-- statement:
--   The Raises construction uses the eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L170-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ConnPhiExtensionGeneratorEqZeta.lean#L170-L179

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
omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.BK.Raises.eq_zero {T : Module.End K (Vec K a ι)} (hT : Raises T) {α : Type}
    {σ : α → α} (hσ : Function.Surjective σ) {δ : α → Vec K a ι} (h1 : ∀ x, δ x ∈ uPow K a ι 1)
    (h : ∀ x, δ (σ x) = T (δ x)) (x : α) : δ x = 0 := by sorry
