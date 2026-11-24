-- Prove2me | Theorems.Thm_GlobalTheory_VeryAmplePow_valuative
-- name    : GlobalTheory.VeryAmplePow.valuative
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:51:15.184984+00:00
-- url     : https://prove2.me/theorems/fa849c6b-f5c9-4650-86d9-81d62e9d797b
-- title:
--   Very Ample Pow: valuative
-- statement:
--   The Very Ample Pow construction uses the valuative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L183-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L183-L218

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
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
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem GlobalTheory.VeryAmplePow.valuative {Y : Scheme.{0}} {M : LB Y} {I : Type} (s : I → LB.Sec M) (hcov : ⨆ i, nonzeroLocus (s i) = ⊤)
    (i : I) (ρ : I → Γ(Y, nonzeroLocus (s i)))
    (hρ : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : M.ι), r z ∈ nonzeroLocus (s i) → r z ∈ M.U k →
      gs r z _ ((s j).f k) = gs r z _ (ρ j) * gs r z _ ((s i).f k))
    (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (l : Spec (.of V) ⟶ Y) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l) ⁻¹ᵁ nonzeroLocus (s i))
    (H : ∀ j, ∃ a : Γ(Spec (.of V), ⊤), (Spec.map (CommRingCat.ofHom (algebraMap V K))).appTop.hom a =
        ((Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l).appLE _ ⊤ h).hom (ρ j)) :
    ⊤ ≤ l ⁻¹ᵁ nonzeroLocus (s i) := by sorry
