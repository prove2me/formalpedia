-- Prove2me | Theorems.Thm_GlobalTheory_SS_exists_pow_factor_free
-- name    : GlobalTheory.SS.exists_pow_factor_free
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:37:34.447177+00:00
-- url     : https://prove2.me/theorems/0b8b9472-a996-40c1-832f-629804ae7c64
-- title:
--   SS: exists pow factor free
-- statement:
--   The SS construction uses the exists pow factor free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DefectBounded.lean#L15-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DefectBounded.lean#L15-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBounded
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
open GlobalTheory GlobalTheory.SS

theorem GlobalTheory.SS.exists_pow_factor_free {B S M M' : Type} [CommRing B] [CommRing S] [Algebra B S] (b : B)
    [IsLocalization (Submonoid.powers b) S] [AddCommGroup M] [Module B M] [Module.FinitePresentation B M]
    [AddCommGroup M'] [Module B M'] [Module S M'] [IsScalarTower B S M'] [Module.Projective S M']
    (f : M →ₗ[B] M') [IsLocalizedModule (Submonoid.powers b) f] :
    ∃ (c n : ℕ) (s : M →ₗ[B] (Fin n → B)) (t : (Fin n → B) →ₗ[B] M), t ∘ₗ s = b ^ c • LinearMap.id := by sorry
