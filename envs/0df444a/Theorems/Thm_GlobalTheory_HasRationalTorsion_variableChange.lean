-- Prove2me | Theorems.Thm_GlobalTheory_HasRationalTorsion_variableChange
-- name    : GlobalTheory.HasRationalTorsion.variableChange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:36:55.971685+00:00
-- url     : https://prove2.me/theorems/a09fe5cf-fdb4-4548-af24-ddecae8bca7f
-- title:
--   Has Rational Torsion: variable Change
-- statement:
--   The Has Rational Torsion construction uses the variable Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L35-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L35-L53

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
variable {K : Type*} [Field K]
variable {W : WeierstrassCurve K} {L : Type*} [Field L] [Algebra K L] {m n : ℕ}

theorem GlobalTheory.HasRationalTorsion.variableChange (h : HasRationalTorsion W L n) (C : VariableChange K) :
    HasRationalTorsion (C • W) L n := by sorry
