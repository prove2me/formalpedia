-- Prove2me | Theorems.Thm_GlobalTheory_SmoothThickenings_mem_smoothLocus
-- name    : GlobalTheory.SmoothThickenings.mem_smoothLocus
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:04:29.91765+00:00
-- url     : https://prove2.me/theorems/d61ecf3a-8e99-4ee9-a220-5b89ce14d706
-- title:
--   Smooth Thickenings: mem smooth Locus
-- statement:
--   The Smooth Thickenings construction uses the mem smooth Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SmoothOfSmoothThickenings.lean#L16-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SmoothOfSmoothThickenings.lean#L16-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsSmoothAtOfSmoothModIdealPowersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothOfSmoothThickenings
import Theorems.Thm_GlobalTheory_SmoothLimit_mem_smoothLocus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SmoothThickenings

theorem GlobalTheory.SmoothThickenings.mem_smoothLocus {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (I : Ideal V) (hI : I ≠ ⊤)
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [LocallyOfFinitePresentation f]
    (h : ∀ e, Smooth (pullback.snd f (thick V I e)))
    (x : X) (hx : f x = IsLocalRing.closedPoint V) : x ∈ f.smoothLocus := by sorry
