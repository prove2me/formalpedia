-- Prove2me | Theorems.Thm_GlobalTheory_HasRationalTorsion_exists_splitCurve_sq
-- name    : GlobalTheory.HasRationalTorsion.exists_splitCurve_sq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:20.59622+00:00
-- url     : https://prove2.me/theorems/dc588290-7e2e-4d3f-b9a8-335a85bb1982
-- title:
--   Has Rational Torsion: exists split Curve sq
-- statement:
--   The Has Rational Torsion construction uses the exists split Curve sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L327-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L327-L349

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

theorem GlobalTheory.HasRationalTorsion.exists_splitCurve_sq (h : HasRationalTorsion W L 4) :
    ∃ (C : VariableChange K) (A B a c : K), C.u = 1 ∧ C • W = splitCurve A B ∧ a ^ 2 = A ∧
      c ^ 2 = A * B * (A - B) := by sorry
