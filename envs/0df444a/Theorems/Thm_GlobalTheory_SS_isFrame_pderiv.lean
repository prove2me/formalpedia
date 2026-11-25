-- Prove2me | Theorems.Thm_GlobalTheory_SS_isFrame_pderiv
-- name    : GlobalTheory.SS.isFrame_pderiv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:00.53467+00:00
-- url     : https://prove2.me/theorems/0f7a7a8a-1dbf-4591-9377-4127e0f015cd
-- title:
--   SS: is Frame pderiv
-- statement:
--   The SS construction uses the is Frame pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/OfDerivationFnOn.lean#L309-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/OfDerivationFnOn.lean#L309-L330

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
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
noncomputable section
open GlobalTheory GlobalTheory.SS
variable (R : Type) [CommRing R] {K : Type} [Field K] [Algebra R K]
variable {R} {A A' : Over (Sp K)}
variable {B : Type} [CommRing B] [Algebra K B]

theorem GlobalTheory.SS.isFrame_pderiv (n : ℕ) :
    IsFrame (A := Over.mk (spMap (algebraMap K (MvPolynomial (Fin n) K))))
      (fun i : Fin n => VF.ofDerivation (MvPolynomial.pderiv i)) := by sorry
