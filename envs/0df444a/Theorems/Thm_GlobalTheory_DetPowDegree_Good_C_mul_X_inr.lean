-- Prove2me | Theorems.Thm_GlobalTheory_DetPowDegree_Good_C_mul_X_inr
-- name    : GlobalTheory.DetPowDegree.Good.C_mul_X_inr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:14.816017+00:00
-- url     : https://prove2.me/theorems/300b109b-cda8-449d-ba6c-bd8f30d3c0d6
-- title:
--   Good: C mul X inr
-- statement:
--   The Good construction uses the C mul X inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetFrobeniusSubPowSupport.lean#L127-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetFrobeniusSubPowSupport.lean#L127-L136

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

theorem GlobalTheory.DetPowDegree.Good.C_mul_X_inr (a : α) :
    Good l L E 1 L 0 (MvPolynomial.C (l ^ E) * X (Sum.inr a) : MvPolynomial (α ⊕ α) ℤ) := by sorry
