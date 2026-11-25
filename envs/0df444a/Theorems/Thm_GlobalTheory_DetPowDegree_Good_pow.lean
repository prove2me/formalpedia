-- Prove2me | Theorems.Thm_GlobalTheory_DetPowDegree_Good_pow
-- name    : GlobalTheory.DetPowDegree.Good.pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:40.708703+00:00
-- url     : https://prove2.me/theorems/3ec893d8-3d4c-46ff-bb32-2a306b651091
-- title:
--   Good: pow
-- statement:
--   The Good construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetFrobeniusSubPowSupport.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetFrobeniusSubPowSupport.lean#L86-L90

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

theorem GlobalTheory.DetPowDegree.Good.pow {n d s : ℕ} {p : MvPolynomial (α ⊕ α) ℤ} (hp : Good l L E n d s p) (k : ℕ) :
    Good l L E (n * k) (d * k) (s * k) (p ^ k) := by sorry
