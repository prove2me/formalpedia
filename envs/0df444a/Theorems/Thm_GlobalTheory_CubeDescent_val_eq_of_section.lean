-- Prove2me | Theorems.Thm_GlobalTheory_CubeDescent_val_eq_of_section
-- name    : GlobalTheory.CubeDescent.val_eq_of_section
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:28:28.108806+00:00
-- url     : https://prove2.me/theorems/1acaa9d1-4edf-4237-bc98-b155112c4a6d
-- title:
--   Cube Descent: val eq of section
-- statement:
--   The Cube Descent construction uses the val eq of section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CubeDescendsAlongEtaleIsogeny.lean#L94-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CubeDescendsAlongEtaleIsogeny.lean#L94-L105

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
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
open GlobalTheory GlobalTheory.CubeDescent
variable {S X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {Q : Over S}
  {φ : K → (Q.left ⟶ X)} {ε : K → ℤ}

theorem GlobalTheory.CubeDescent.val_eq_of_section (hL : L.IsLB) {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen)
    {P T : Over S} (p : P ⟶ T) (e : T ⟶ P) (he : e ≫ p = 𝟙 T)
    (hp : Function.Surjective p.left.appTop.hom) (a a' : P ⟶ Q)
    (hF : FormEq (fun k => a'.left ≫ φ k) ε (fun k => a.left ≫ φ k) ε)
    (h : ∀ y J, Good L y J → val u (e ≫ a).left y J = val u (e ≫ a').left y J)
    {T' : Over S} (ρ : T' ⟶ P) (z : T'.left) (J) (hJ : Good L z J) :
    val u (ρ ≫ a).left z J = val u (ρ ≫ a').left z J := by sorry
