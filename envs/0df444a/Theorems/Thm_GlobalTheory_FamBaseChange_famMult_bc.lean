-- Prove2me | Theorems.Thm_GlobalTheory_FamBaseChange_famMult_bc
-- name    : GlobalTheory.FamBaseChange.famMult_bc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:17:49.493332+00:00
-- url     : https://prove2.me/theorems/75aedd49-cddf-4a5e-9f2b-719081b36f0d
-- title:
--   Fam Base Change: fam Mult bc
-- statement:
--   The Fam Base Change construction uses the fam Mult bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntegralDegenerationFamilyBaseChangeExtensionFie.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntegralDegenerationFamilyBaseChangeExtensionFie.lean#L46-L52

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

theorem GlobalTheory.FamBaseChange.famMult_bc (k : ℕ) (α mu : D.X) (y : (DegPre.BF D F).left) {J} (hJ : Good D.P.L y J) :
    val (DegPre.famMult D (FractionRing R) k mu α) (bc D F ≫ fst _ _).left y J =
      val (DegPre.famMult D F k mu α) (𝟙 (DegPre.BF D F) ≫ fst _ _).left y J := by sorry
