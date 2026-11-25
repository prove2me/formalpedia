-- Prove2me | Theorems.Thm_GlobalTheory_DetPowDegree_X_inr_mem_freeIdeal
-- name    : GlobalTheory.DetPowDegree.X_inr_mem_freeIdeal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:21.268924+00:00
-- url     : https://prove2.me/theorems/85db93d2-c2e6-44ce-880e-8744be5a80b8
-- title:
--   Det Pow Degree: X inr mem free Ideal
-- statement:
--   The Det Pow Degree construction uses the X inr mem free Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetFrobeniusSubPowSupport.lean#L158-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetFrobeniusSubPowSupport.lean#L158-L166

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

theorem GlobalTheory.DetPowDegree.X_inr_mem_freeIdeal (a : α) :
    (X (Sum.inr a) : MvPolynomial (α ⊕ α) ℤ) ∈ freeIdeal α l := by sorry
