-- Prove2me | Theorems.Thm_GlobalTheory_HasRationalTorsion_exists_splitCurve
-- name    : GlobalTheory.HasRationalTorsion.exists_splitCurve
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:19.757801+00:00
-- url     : https://prove2.me/theorems/10abf857-e668-4cb3-9e5a-eab5e85b264b
-- title:
--   Has Rational Torsion: exists split Curve
-- statement:
--   The Has Rational Torsion construction uses the exists split Curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L244-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L244-L275

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

theorem GlobalTheory.HasRationalTorsion.exists_splitCurve (h : HasRationalTorsion W L 2) :
    ∃ (C : VariableChange K) (A B : K), C.u = 1 ∧ C • W = splitCurve A B := by sorry
