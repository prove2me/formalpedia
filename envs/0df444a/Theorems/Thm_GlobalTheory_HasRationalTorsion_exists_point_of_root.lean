-- Prove2me | Theorems.Thm_GlobalTheory_HasRationalTorsion_exists_point_of_root
-- name    : GlobalTheory.HasRationalTorsion.exists_point_of_root
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:12.673782+00:00
-- url     : https://prove2.me/theorems/2df1e34e-80fa-4bb1-b60a-8ad175e788eb
-- title:
--   Has Rational Torsion: exists point of root
-- statement:
--   The Has Rational Torsion construction uses the exists point of root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L173-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L173-L183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {K : Type*} [Field K] [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]
omit [CharZero K]

theorem GlobalTheory.HasRationalTorsion.exists_point_of_root (h : HasRationalTorsion W L 3) {x : L}
    (hx : (W.baseChange L).Ψ₃.eval x = 0) :
    ∃ x₀ y₀ : K, algebraMap K L x₀ = x ∧ W.toAffine.Nonsingular x₀ y₀ ∧ W.Ψ₃.eval x₀ = 0 := by sorry
