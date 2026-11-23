-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wd_cons
-- name    : GlobalTheory.SmoothForms.PermWord.wd_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:09.833884+00:00
-- url     : https://prove2.me/theorems/465f2d08-3417-494c-b52f-845bed8d6a83
-- title:
--   Perm Word: wd cons
-- statement:
--   The Perm Word construction uses the wd cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L92-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.PermWord
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem GlobalTheory.SmoothForms.PermWord.wd_cons {B : Type} [Ring B] (E : Fin n → Fin n → B) (z) (l : List (Fin n × Fin n)) :
    wd E (z :: l) = E z.1 z.2 * wd E l := by sorry
