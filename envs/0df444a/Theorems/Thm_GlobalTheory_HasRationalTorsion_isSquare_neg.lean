-- Prove2me | Theorems.Thm_GlobalTheory_HasRationalTorsion_isSquare_neg
-- name    : GlobalTheory.HasRationalTorsion.isSquare_neg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:12.279986+00:00
-- url     : https://prove2.me/theorems/074e9bbe-1e55-466d-ae57-e45d638dffaf
-- title:
--   Has Rational Torsion: is Square neg
-- statement:
--   The Has Rational Torsion construction uses the is Square neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L279-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L279-L325

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

theorem GlobalTheory.HasRationalTorsion.isSquare_neg {A B : K} [(splitCurve A B).IsElliptic]
    (h : HasRationalTorsion (splitCurve A B) L 4) : ∃ a : K, a ^ 2 = -A := by sorry
