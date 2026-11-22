-- Prove2me | Theorems.Thm_GlobalTheory_hasRationalTorsion_iff
-- name    : GlobalTheory.hasRationalTorsion_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:36:38.663496+00:00
-- url     : https://prove2.me/theorems/7acb668e-fdeb-4398-8eb7-a919219e5f94
-- title:
--   Global Theory: has Rational Torsion iff
-- statement:
--   The Global Theory construction uses the has Rational Torsion iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L21-L25

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

theorem GlobalTheory.hasRationalTorsion_iff [DecidableEq L] : HasRationalTorsion W L n ↔
    ∀ (x y : L) (h : (W.baseChange L).toAffine.Nonsingular x y), n • Point.some x y h = 0 →
      x ∈ (algebraMap K L).range ∧ y ∈ (algebraMap K L).range := by sorry
