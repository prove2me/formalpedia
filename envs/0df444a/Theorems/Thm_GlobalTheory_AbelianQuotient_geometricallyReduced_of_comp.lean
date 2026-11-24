-- Prove2me | Theorems.Thm_GlobalTheory_AbelianQuotient_geometricallyReduced_of_comp
-- name    : GlobalTheory.AbelianQuotient.geometricallyReduced_of_comp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:52:23.050955+00:00
-- url     : https://prove2.me/theorems/f162dead-0516-49fb-b819-f6fb19d38cff
-- title:
--   Abelian Quotient: geometrically Reduced of comp
-- statement:
--   The Abelian Quotient construction uses the geometrically Reduced of comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuotientIsAbelianSchemeOfQuotientScheme.lean#L163-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuotientIsAbelianSchemeOfQuotientScheme.lean#L163-L168

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.AbelianQuotient
variable {S : Scheme.{0}}

theorem GlobalTheory.AbelianQuotient.geometricallyReduced_of_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z) [Flat p]
    [Surjective p] [h : GeometricallyReduced (p ≫ f)] : GeometricallyReduced f := by sorry
