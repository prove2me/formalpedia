-- Prove2me | Theorems.Thm_GlobalTheory_AffineLineExt_extend
-- name    : GlobalTheory.AffineLineExt.extend
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:54:54.142984+00:00
-- url     : https://prove2.me/theorems/44d33e8f-fb26-46e9-8045-8d7b43b2c2aa
-- title:
--   Affine Line Ext: extend
-- statement:
--   The Affine Line Ext construction uses the extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtendAffineLineMorphismToProperAcrossPoint.lean#L19-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtendAffineLineMorphismToProperAcrossPoint.lean#L19-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAffineLineMorphismToProperAcrossPoint
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
open GlobalTheory GlobalTheory.AffineLineExt
open Polynomial

theorem GlobalTheory.AffineLineExt.extend : ∀ (k : Type) [Field k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k) (c : k), P ≠ 0 → ∀ u : Sp (Localization.Away (P * (Polynomial.X - Polynomial.C c))) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away (P * (Polynomial.X - Polynomial.C c)))) → ∃ v : Sp (Localization.Away P) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P) (P := Localization.Away (P * (Polynomial.X - Polynomial.C c))) P (Polynomial.X - Polynomial.C c)) ≫ v = u := by sorry
