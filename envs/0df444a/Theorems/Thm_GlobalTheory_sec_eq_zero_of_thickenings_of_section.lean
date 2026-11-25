-- Prove2me | Theorems.Thm_GlobalTheory_sec_eq_zero_of_thickenings_of_section
-- name    : GlobalTheory.sec_eq_zero_of_thickenings_of_section
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:53:34.693801+00:00
-- url     : https://prove2.me/theorems/7385118f-66f0-4d9c-8ac7-fffbc8d5d3f6
-- title:
--   Global Theory: sec eq zero of thickenings of section
-- statement:
--   The Global Theory construction uses the sec eq zero of thickenings of section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqZeroOfThickeningsOfSection.lean#L19-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SecEqZeroOfThickeningsOfSection.lean#L19-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ThickeningDetermines

theorem GlobalTheory.sec_eq_zero_of_thickenings_of_section (R : Type) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R)))
    [Smooth H.hom] [GeometricallyConnected H.hom] (e : 𝟙_ _ ⟶ H) (N : LB H.left) (hN : N.IsLB)
    (s : LB.Sec N) (hs : ∀ (n : ℕ) j, ((fstG I n H).left.app _).hom (s.f j) = 0) (j) :
    s.f j = 0 := by sorry
