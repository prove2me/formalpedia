-- Prove2me | Theorems.Thm_GlobalTheory_BK_Lc_rankOneDat
-- name    : GlobalTheory.BK.Lc_rankOneDat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:01:39.430645+00:00
-- url     : https://prove2.me/theorems/cb9e7a3c-5037-5985-9b7d-dd0a9fef03c8
-- title:
--   BK: Lc rank One Dat
-- statement:
--   The BK construction uses the Lc rank One Dat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L358-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsAlgebraMapEqRoot.lean#L358-L380

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
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
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}
variable [CompleteSpace K] {j : ℤ} (h₁ : -(η : ℤ) ≤ j) (h₂ : j ≤ H)

theorem GlobalTheory.BK.Lc_rankOneDat (χ : TameGal K l e a →* O) :
    (rankOneDat O K l e a η H j h₁ h₂ χ).Lc
        ((rankOneDat O K l e a η H j h₁ h₂ χ).cls (Ezpow K l e (-1) • bas ())) =
      (((j + 1) * e * l : ℤ) : K) •
        (rankOneDat O K l e a η H j h₁ h₂ χ).cls (Ezpow K l e (-1) • bas ()) := by sorry
