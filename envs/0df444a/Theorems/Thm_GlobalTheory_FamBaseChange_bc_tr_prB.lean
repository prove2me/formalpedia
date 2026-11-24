-- Prove2me | Theorems.Thm_GlobalTheory_FamBaseChange_bc_tr_prB
-- name    : GlobalTheory.FamBaseChange.bc_tr_prB
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:18:10.418328+00:00
-- url     : https://prove2.me/theorems/5dfb0d1f-101f-449e-9fea-d1ef54a733d5
-- title:
--   Fam Base Change: bc tr pr B
-- statement:
--   The Fam Base Change construction uses the bc tr pr B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntegralDegenerationFamilyBaseChangeExtensionFie.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntegralDegenerationFamilyBaseChangeExtensionFie.lean#L37-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntegralDegenerationFamilyBaseChangeExtensionFie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.FamBaseChange.bc_tr_prB (mu : D.X) :
    bc D F ≫ DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) =
      DegPre.trF D F mu ≫ DegPre.prB D F := by sorry
