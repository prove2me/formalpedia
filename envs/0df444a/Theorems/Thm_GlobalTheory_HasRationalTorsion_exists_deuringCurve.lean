-- Prove2me | Theorems.Thm_GlobalTheory_HasRationalTorsion_exists_deuringCurve
-- name    : GlobalTheory.HasRationalTorsion.exists_deuringCurve
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:59.53417+00:00
-- url     : https://prove2.me/theorems/441be2d3-85ae-4364-bc0d-f37e9d5a3834
-- title:
--   Has Rational Torsion: exists deuring Curve
-- statement:
--   The Has Rational Torsion construction uses the exists deuring Curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L185-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L185-L227

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

theorem GlobalTheory.HasRationalTorsion.exists_deuringCurve (h : HasRationalTorsion W L 3) :
    ∃ (C : VariableChange K) (a b d : K), C.u = 1 ∧ C • W = deuringCurve a b ∧
      d ^ 3 = a ^ 3 - 27 * b := by sorry
