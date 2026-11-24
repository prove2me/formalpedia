-- Prove2me | Theorems.Thm_GlobalTheory_SquareDensity_dvd_aeval_sub_aeval
-- name    : GlobalTheory.SquareDensity.dvd_aeval_sub_aeval
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:22:43.506064+00:00
-- url     : https://prove2.me/theorems/00153339-36af-4fa3-96ec-0144a19c2249
-- title:
--   Square Density: dvd aeval sub aeval
-- statement:
--   The Square Density construction uses the dvd aeval sub aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSqAddSubDvd.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSqAddSubDvd.lean#L27-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSqAddSubDvd
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GlobalTheory.SquareDensity

theorem GlobalTheory.SquareDensity.dvd_aeval_sub_aeval {K S σ : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (Φ : MvPolynomial σ K) (s : S) (a b : σ → S) (h : ∀ i, s ∣ a i - b i) :
    s ∣ MvPolynomial.aeval a Φ - MvPolynomial.aeval b Φ := by sorry
