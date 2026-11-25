-- Prove2me | Theorems.Thm_GlobalTheory_TorsionIntegral_exists_gen_extend
-- name    : GlobalTheory.TorsionIntegral.exists_gen_extend
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T16:18:31.3398+00:00
-- url     : https://prove2.me/theorems/a16da184-3411-4e86-b2fc-7f971c08f530
-- title:
--   Torsion Integral: exists gen extend
-- statement:
--   The Torsion Integral construction uses the exists gen extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean#L170-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean#L170-L181

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

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
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open GlobalTheory.TorsionIntegral
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem GlobalTheory.TorsionIntegral.exists_gen_extend (hL : L.IsLB) (φ : Z ⟶ Y) (z : Z) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) {ψ' : K → (Z ⟶ X)}
    (hψ : ∀ k, ψ' k = φ ≫ ψ k) {J₀ : (Z ⟶ X) → L.ι} (hJ₀ : Good L z J₀)
    (h₀ : ∀ (q : Y ⟶ X) (y : Y), q y ∈ L.U (J₀ (φ ≫ q))) (t : LB.Gen (LB.LinComb L ψ' ε)) (ht : t.IsGen)
    (hv : val t (𝟙 Z) z J₀ ∈ (gm φ z ⊤).range) :
    ∃ t' : LB.Gen (LB.LinComb L ψ ε), t'.IsGen ∧ ∀ J, Good L z J → val t' φ z J = val t (𝟙 Z) z J := by sorry
