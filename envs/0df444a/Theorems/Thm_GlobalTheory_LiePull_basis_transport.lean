-- Prove2me | Theorems.Thm_GlobalTheory_LiePull_basis_transport
-- name    : GlobalTheory.LiePull.basis_transport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:46.507945+00:00
-- url     : https://prove2.me/theorems/457f4b84-361f-4f5f-a66d-a7954a817913
-- title:
--   Lie Pull: basis transport
-- statement:
--   The Lie Pull construction uses the basis transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsPushEquiv.lean#L24-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsPushEquiv.lean#L24-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

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
open GlobalTheory GlobalTheory.LiePull

theorem GlobalTheory.LiePull.basis_transport {A B k : Type} [Monoid A] [Monoid B] (e : A ≃* B) {P : A → Prop} {Q : B → Prop}
    {R : k → A → A → Prop} {R' : k → B → B → Prop} (hP : ∀ x, P x ↔ Q (e x))
    (hR : ∀ c x y, R c x y ↔ R' c (e x) (e y)) (n : ℕ)
    (H : ∃ v : Fin n → A, (∀ i, P (v i)) ∧ ∀ w, P w →
      ∃! c : Fin n → k, ∃ u : Fin n → A, (∀ i, R (c i) (u i) (v i)) ∧ w = (List.ofFn u).prod) :
    ∃ v : Fin n → B, (∀ i, Q (v i)) ∧ ∀ w, Q w →
      ∃! c : Fin n → k, ∃ u : Fin n → B, (∀ i, R' (c i) (u i) (v i)) ∧ w = (List.ofFn u).prod := by sorry
