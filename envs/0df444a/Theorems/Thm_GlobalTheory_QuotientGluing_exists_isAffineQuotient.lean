-- Prove2me | Theorems.Thm_GlobalTheory_QuotientGluing_exists_isAffineQuotient
-- name    : GlobalTheory.QuotientGluing.exists_isAffineQuotient
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:14.271377+00:00
-- url     : https://prove2.me/theorems/1ed58e4b-e224-4895-ac97-7fc34ac7cba7
-- title:
--   Quotient Gluing: exists is Affine Quotient
-- statement:
--   The Quotient Gluing construction uses the exists is Affine Quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientOfFiniteGroup.lean#L203-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientOfFiniteGroup.lean#L203-L221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientOfFiniteGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.QuotientGluing
variable {G : Type} [Group G] [Finite G] {X : Scheme.{0}}

theorem GlobalTheory.QuotientGluing.exists_isAffineQuotient (ρ : G →* Aut X) [OrbitsInAffineOpens ρ] :
    ∃ (X' : Scheme.{0}) (π : X ⟶ X'), IsAffineQuotient ρ π := by sorry
