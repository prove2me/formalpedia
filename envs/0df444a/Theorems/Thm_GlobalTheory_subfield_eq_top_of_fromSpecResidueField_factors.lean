-- Prove2me | Theorems.Thm_GlobalTheory_subfield_eq_top_of_fromSpecResidueField_factors
-- name    : GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:21:44.480236+00:00
-- url     : https://prove2.me/theorems/e7ba0c01-a68a-4be1-ac11-c1b12538af5a
-- title:
--   Global Theory: subfield eq top of from Spec Residue Field factors
-- statement:
--   The Global Theory construction uses the subfield eq top of from Spec Residue Field factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullbackResidueFieldsGenerate.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullbackResidueFieldsGenerate.lean#L8-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullbackResidueFieldsGenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory
open CategoryTheory Limits AlgebraicGeometry

theorem GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors (Z : Scheme.{0}) (t : Z)
    (K : Subfield (Z.residueField t)) (m : Spec (CommRingCat.of K) ⟶ Z)
    (hm : Spec.map (CommRingCat.ofHom K.subtype) ≫ m = Z.fromSpecResidueField t) : K = ⊤ := by sorry
