-- Prove2me | Theorems.Thm_GlobalTheory_DetPowDegree_Good_X_inl
-- name    : GlobalTheory.DetPowDegree.Good.X_inl
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:35.529303+00:00
-- url     : https://prove2.me/theorems/b1ec2692-2403-47d6-9e1e-b907165a256d
-- title:
--   Good: X inl
-- statement:
--   The Good construction uses the X inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetFrobeniusSubPowSupport.lean#L117-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetFrobeniusSubPowSupport.lean#L117-L125

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

theorem GlobalTheory.DetPowDegree.Good.X_inl (a : α) : Good l L E 0 1 0 (X (Sum.inl a) : MvPolynomial (α ⊕ α) ℤ) := by sorry
