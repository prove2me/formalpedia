-- Prove2me | Theorems.Thm_GlobalTheory_nonsingular_baseChange_iff
-- name    : GlobalTheory.nonsingular_baseChange_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:35.912622+00:00
-- url     : https://prove2.me/theorems/762c1290-6eb1-4eb2-b3e7-96cf5fa3d32a
-- title:
--   Global Theory: nonsingular base Change iff
-- statement:
--   The Global Theory construction uses the nonsingular base Change iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L94-L98

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

theorem GlobalTheory.nonsingular_baseChange_iff {K : Type*} [Field K] {W : WeierstrassCurve K} [W.IsElliptic]
    {L : Type*} [Field L] [Algebra K L] {x y : L} :
    (W.baseChange L).toAffine.Nonsingular x y ↔ (W.baseChange L).toAffine.Equation x y := by sorry
