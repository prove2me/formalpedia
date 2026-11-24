-- Prove2me | Theorems.Thm_GlobalTheory_gm_mul_eq_of_res_mul_eq
-- name    : GlobalTheory.gm_mul_eq_of_res_mul_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:34.150798+00:00
-- url     : https://prove2.me/theorems/bb9b79ac-eabc-4c85-a959-66b2edda9938
-- title:
--   Global Theory: gm mul eq of res mul eq
-- statement:
--   The Global Theory construction uses the gm mul eq of res mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GmMulEqOfResMulEq.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GmMulEqOfResMulEq.lean#L18-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmMulEqOfResMulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.gm_mul_eq_of_res_mul_eq {Y Z : Scheme.{0}} {V U₁ U₂ U₃ U₄ : Y.Opens} {h₁ : V ≤ U₁} {h₂ : V ≤ U₂}
    {h₃ : V ≤ U₃} {h₄ : V ≤ U₄} {a : Γ(Y, U₁)ˣ} {b : Γ(Y, U₂)ˣ} {c : Γ(Y, U₃)ˣ} {d : Γ(Y, U₄)ˣ}
    (H : res h₁ a * res h₂ b = res h₃ c * res h₄ d) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ V) :
    gm r z U₁ a * gm r z U₂ b = gm r z U₃ c * gm r z U₄ d := by sorry
