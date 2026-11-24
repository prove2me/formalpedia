-- Prove2me | Theorems.Thm_GlobalTheory_ZH_ConePrime_map_coneHom
-- name    : GlobalTheory.ZH.ConePrime.map_coneHom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:03:30.788704+00:00
-- url     : https://prove2.me/theorems/4d70e707-5d87-4f00-86aa-2d56dd544794
-- title:
--   Cone Prime: map cone Hom
-- statement:
--   The Cone Prime construction uses the map cone Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VanishingIdealConePrimeHomogeneous.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VanishingIdealConePrimeHomogeneous.lean#L28-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.ConePrime
open GlobalTheory.ZH.CrdCalc GlobalTheory.TangentOrigin
variable {k J A B : Type} [CommRing k] [CommRing A] [CommRing B]

theorem GlobalTheory.ZH.ConePrime.map_coneHom (c : k →+* A) (r : J → A) (e : A →+* B) (f : MvPolynomial J k) :
    Polynomial.map e (coneHom c r f) = coneHom (e.comp c) (fun j => e (r j)) f := by sorry
