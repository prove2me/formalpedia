-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_multiplicativeGroup_open_nonvanishing_polynomial
-- name    : GlobalTheory.T.exists_multiplicativeGroup_open_nonvanishing_polynomial
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:49:39.939305+00:00
-- url     : https://prove2.me/theorems/fd0c1150-d787-4dcb-8d43-96b59df06cc2
-- title:
--   T: exists multiplicative Group open nonvanishing polynomial
-- statement:
--   The T construction uses the exists multiplicative Group open nonvanishing polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsMultiplicativeGroupOpenNonvanishingPolynomStatement.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsMultiplicativeGroupOpenNonvanishingPolynomStatement.lean#L16-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsMultiplicativeGroupOpenNonvanishingPolynom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsMultiplicativeGroupOpenNonvanishingPolynomStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_multiplicativeGroup_open_nonvanishing_polynomial : ∀ (k : Type) [Field k] (q : Polynomial k), ∃ jj : algOver k (Localization.Away (Polynomial.X * q)) ⟶ Gm (Sp k), IsOpenImmersion jj.left ∧ ∀ x y z : Localization.Away (Polynomial.X * q) →ₐ[k] k, (algOverHom x ≫ jj) * (algOverHom y ≫ jj) = algOverHom z ≫ jj → x (algebraMap (Polynomial k) _ Polynomial.X) * y (algebraMap (Polynomial k) _ Polynomial.X) = z (algebraMap (Polynomial k) _ Polynomial.X) := by sorry
