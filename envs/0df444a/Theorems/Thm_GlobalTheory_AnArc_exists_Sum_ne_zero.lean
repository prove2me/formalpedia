-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_exists_Sum_ne_zero
-- name    : GlobalTheory.AnArc.exists_Sum_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:18.116598+00:00
-- url     : https://prove2.me/theorems/422f4815-4918-43a4-b12f-f26b560c3399
-- title:
--   An Arc: exists Sum ne zero
-- statement:
--   The An Arc construction uses the exists Sum ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L633-L637
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L633-L637

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.exists_Sum_ne_zero {j : ℕ} (hj : j ≠ 0) (α : A.X) {th : (Fin A.gB → ℂ) → ℂ} (h : th ≠ 0) {w : ℂ}
    (hs : ∀ z, Summable fun μ => A.term j α th μ (0, z) * eTwoPi (w * A.exponent j α μ)) :
    ∃ v, A.Sum j α th w v ≠ 0 := by sorry
