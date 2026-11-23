-- Prove2me | Theorems.Thm_GlobalTheory_values_natural
-- name    : GlobalTheory.values_natural
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:46:18.337342+00:00
-- url     : https://prove2.me/theorems/914e07b6-cea4-413b-84ea-2eb3e2028b3c
-- title:
--   Global Theory: values natural
-- statement:
--   The Global Theory construction uses the values natural property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ValuesNatural.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ValuesNatural.lean#L21-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural
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

theorem GlobalTheory.values_natural : ∀ (X Y Z Z' : Scheme.{0}) (L : LB X) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (ρ : Z' ⟶ Z) (z : Z') (J : (Z' ⟶ X) → L.ι), Good L z J → Good L (ρ z) (fun ψ : Z ⟶ X => J (ρ ≫ ψ)) ∧ (∀ s : LB.Sec (LB.LinComb L φ ε), sval s (ρ ≫ r) z J = (ρ.stalkMap z).hom (sval s r (ρ z) (fun ψ => J (ρ ≫ ψ)))) ∧ (∀ t : LB.Gen (LB.LinComb L φ ε), (val t (ρ ≫ r) z J).val = (ρ.stalkMap z).hom (val t r (ρ z) (fun ψ => J (ρ ≫ ψ))).val) ∧ ∀ c : Γ(Y, ⊤), gs (ρ ≫ r) z ⊤ c = (ρ.stalkMap z).hom (gs r (ρ z) ⊤ c) := by sorry
