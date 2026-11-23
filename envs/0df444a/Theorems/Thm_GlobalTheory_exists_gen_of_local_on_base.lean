-- Prove2me | Theorems.Thm_GlobalTheory_exists_gen_of_local_on_base
-- name    : GlobalTheory.exists_gen_of_local_on_base
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:13.721736+00:00
-- url     : https://prove2.me/theorems/3e10b7a2-839d-41dc-98a1-1ee166414ca0
-- title:
--   Global Theory: exists gen of local on base
-- statement:
--   The Global Theory construction uses the exists gen of local on base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfLocalOnBase.lean#L14-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfLocalOnBase.lean#L14-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.exists_gen_of_local_on_base {X Y S : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Y ⟶ S) (e : S ⟶ Y) (he : e ≫ p = 𝟙 S)
    (hp : ∀ V : S.Opens, Function.Surjective (pullback.snd p V.ι).appTop.hom)
    (h0 : ∀ (U : Type) [CommGroup U] (h : (S ⟶ X) → U), ∏ k, h (e ≫ φ k) ^ ε k = 1)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen (LB.LinComb L (fun k => (p ⁻¹ᵁ U).ι ≫ φ k) ε), t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen := by sorry
