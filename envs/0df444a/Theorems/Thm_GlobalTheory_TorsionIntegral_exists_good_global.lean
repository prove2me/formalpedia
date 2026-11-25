-- Prove2me | Theorems.Thm_GlobalTheory_TorsionIntegral_exists_good_global
-- name    : GlobalTheory.TorsionIntegral.exists_good_global
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:19:19.70377+00:00
-- url     : https://prove2.me/theorems/51dac941-5f9d-4a36-abcd-798c9ffb2fef
-- title:
--   Torsion Integral: exists good global
-- statement:
--   The Torsion Integral construction uses the exists good global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean#L191-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean#L191-L198

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

theorem GlobalTheory.TorsionIntegral.exists_good_global (hL : L.IsLB) (φ : Z ⟶ Y) (z : Z) (y₀ : Y) (hy₀ : ∀ (U : Y.Opens) (y : Y), y₀ ∈ U → y ∈ U)
    (he : ∀ ψ ψ' : Y ⟶ X, φ ≫ ψ = φ ≫ ψ' → ψ = ψ') :
    ∃ J₀ : (Z ⟶ X) → L.ι, Good L z J₀ ∧ ∀ (q : Y ⟶ X) (y : Y), q y ∈ L.U (J₀ (φ ≫ q)) := by sorry
