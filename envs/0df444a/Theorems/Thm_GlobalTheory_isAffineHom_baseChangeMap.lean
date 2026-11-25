-- Prove2me | Theorems.Thm_GlobalTheory_isAffineHom_baseChangeMap
-- name    : GlobalTheory.isAffineHom_baseChangeMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:06:21.19757+00:00
-- url     : https://prove2.me/theorems/e7fcb9c0-0518-4513-83b7-6334f8f52dde
-- title:
--   Global Theory: is Affine Hom base Change Map
-- statement:
--   The Global Theory construction uses the is Affine Hom base Change Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L371-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L371-L377

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C]
variable {R₀ : Subalgebra k C}
variable {B : Scheme.{0}} (pB : B ⟶ Sp k)
variable {A A' A'' : Type} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] [CommRing A''] [Algebra k A'']

theorem GlobalTheory.isAffineHom_baseChangeMap (f : A →ₐ[k] A') : IsAffineHom (baseChangeMap pB f) := by sorry
