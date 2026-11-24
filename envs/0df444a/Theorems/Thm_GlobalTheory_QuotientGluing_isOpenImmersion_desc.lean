-- Prove2me | Theorems.Thm_GlobalTheory_QuotientGluing_isOpenImmersion_desc
-- name    : GlobalTheory.QuotientGluing.isOpenImmersion_desc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:12:43.797805+00:00
-- url     : https://prove2.me/theorems/e8b74378-f305-454a-98ab-2c3184d31294
-- title:
--   Quotient Gluing: is Open Immersion desc
-- statement:
--   The Quotient Gluing construction uses the is Open Immersion desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientOfFiniteGroup.lean#L18-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientOfFiniteGroup.lean#L18-L37

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

theorem GlobalTheory.QuotientGluing.isOpenImmersion_desc {T T' Y Y' : Scheme.{0}} {σ : G →* Aut T} {σ' : G →* Aut T'}
    {q : T ⟶ Y} {q' : T' ⟶ Y'} (h : IsAffineQuotient σ q) (h' : IsAffineQuotient σ' q')
    (m : T ⟶ T') [IsOpenImmersion m] (hm : ∀ g, (σ g).hom ≫ m = m ≫ (σ' g).hom)
    (k : Y ⟶ Y') (hk : q ≫ k = m ≫ q') : IsOpenImmersion k := by sorry
