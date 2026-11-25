-- Prove2me | Theorems.Thm_GlobalTheory_T_extend_affineLine_morphism_to_proper_across_point
-- name    : GlobalTheory.T.extend_affineLine_morphism_to_proper_across_point
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:50.281187+00:00
-- url     : https://prove2.me/theorems/91296992-c7d6-5f7e-aa16-834a658788b0
-- title:
--   T: extend affine Line morphism to proper across point
-- statement:
--   The T construction uses the extend affine Line morphism to proper across point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtendAffineLineMorphismToProperAcrossPointStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtendAffineLineMorphismToProperAcrossPointStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAffineLineMorphismToProperAcrossPoint
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAffineLineMorphismToProperAcrossPointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.extend_affineLine_morphism_to_proper_across_point : ∀ (k : Type) [Field k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k) (c : k), P ≠ 0 → ∀ u : Sp (Localization.Away (P * (Polynomial.X - Polynomial.C c))) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away (P * (Polynomial.X - Polynomial.C c)))) → ∃ v : Sp (Localization.Away P) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P) (P := Localization.Away (P * (Polynomial.X - Polynomial.C c))) P (Polynomial.X - Polynomial.C c)) ≫ v = u := by sorry
