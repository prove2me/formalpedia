-- Prove2me | Theorems.Thm_GlobalTheory_DetPowDegree_C_dvd_expand_sub_pow
-- name    : GlobalTheory.DetPowDegree.C_dvd_expand_sub_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:12.735795+00:00
-- url     : https://prove2.me/theorems/f48882fd-5a1b-44d3-90f9-3e7a878b72ff
-- title:
--   Det Pow Degree: C dvd expand sub pow
-- statement:
--   The Det Pow Degree construction uses the C dvd expand sub pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetFrobeniusSubPowSupport.lean#L177-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetFrobeniusSubPowSupport.lean#L177-L184

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPolynomial
open GlobalTheory GlobalTheory.DetPowDegree
variable {α : Type} [Fintype α]
variable {l : ℤ} {L E : ℕ}

theorem GlobalTheory.DetPowDegree.C_dvd_expand_sub_pow {σ : Type} (l i : ℕ) (hl : l.Prime) (f : MvPolynomial σ ℤ) :
    MvPolynomial.C (l : ℤ) ∣ expand (l ^ i) f - f ^ (l ^ i) := by sorry
