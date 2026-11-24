-- Prove2me | Theorems.Thm_GlobalTheory_CubeDescent_val_eq_of_axis
-- name    : GlobalTheory.CubeDescent.val_eq_of_axis
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:28:32.171743+00:00
-- url     : https://prove2.me/theorems/552c3523-14cf-423c-82cb-3517e48fd063
-- title:
--   Cube Descent: val eq of axis
-- statement:
--   The Cube Descent construction uses the val eq of axis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CubeDescendsAlongEtaleIsogeny.lean#L109-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CubeDescendsAlongEtaleIsogeny.lean#L109-L137

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
variable {A : Over S} [GrpObj A]

theorem GlobalTheory.CubeDescent.val_eq_of_axis (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (σ : A ⊗ A ⊗ A ⟶ Q)
    (H₁ : FormEq (fun k => (lift (1 : A ⟶ A) (lift 1 1) ≫ σ).left ≫ φ k) ε
      (fun k => (lift (𝟙 A) (lift 1 1) ≫ σ).left ≫ φ k) ε)
    {T : Over S} (x x' : T ⟶ A)
    (H₂ : ∀ (T' : Over S) (ρ : T' ⟶ T) (y w : T' ⟶ A) (k : K),
      (lift (ρ ≫ x') (lift y w) ≫ σ).left ≫ φ k = (lift (ρ ≫ x) (lift y w) ≫ σ).left ≫ φ k)
    (y w : T ⟶ A) (z : T.left) (J) (hJ : Good L z J) :
    val u (lift x (lift y w) ≫ σ).left z J = val u (lift x' (lift y w) ≫ σ).left z J := by sorry
