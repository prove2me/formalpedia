-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_Seesaw_exists_kernel_vector
-- name    : GlobalTheory.AbLaw.Seesaw.exists_kernel_vector
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:08:39.682805+00:00
-- url     : https://prove2.me/theorems/14e2bc41-b53e-4adf-b403-1095e7febd92
-- title:
--   Seesaw: exists kernel vector
-- statement:
--   The Seesaw construction uses the exists kernel vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKernelVector.lean#L37-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKernelVector.lean#L37-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw

theorem GlobalTheory.AbLaw.Seesaw.exists_kernel_vector {R K : Type} [CommRing R] [Field K] (g₀ : R →+* K) {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) R) (v : Fin a → K) (hv : v ≠ 0)
    (hker : ∀ w, (D.map g₀).mulVec w = 0 → ∃ c : K, w = c • v) :
    ∃ (δ : R) (v₀ : Fin a → R), g₀ δ ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g δ) →
      ∀ w, (D.map g).mulVec w = 0 → ∃ c : R', w = c • (g ∘ v₀) := by sorry
