-- Prove2me | Theorems.Thm_GlobalTheory_PushInv_exists_ratio_above
-- name    : GlobalTheory.PushInv.exists_ratio_above
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:00:35.132896+00:00
-- url     : https://prove2.me/theorems/2cc2190c-e9f0-45ca-ba5c-43e0cd8f10ec
-- title:
--   Push Inv: exists ratio above
-- statement:
--   The Push Inv construction uses the exists ratio above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PushInvertibleOfDensePart.lean#L137-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PushInvertibleOfDensePart.lean#L137-L186

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PushInvertibleOfDensePart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.PushInv
open GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.PushInv.exists_ratio_above {U : Scheme.{0}} {j : U ⟶ X} [IsPreimmersion j] {G : Over X} {G₀ : Over U}
    {φ : G₀.left ⟶ G.left} {L : LB G.left} {L₀ : LB G₀.left} (sq : φ ≫ G.hom = G₀.hom ≫ j) (hL : L.IsLB)
    (hL₀ : L₀.IsLB) (hw : LBIso L₀ (L.pull φ)) (h₀ : PushInvertible G₀ L₀) {V W A : X.Opens} (hA : IsAffineOpen A)
    {θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)} (hθ : θ ∈ secOn L (G.hom ⁻¹ᵁ V))
    {s : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ W ⊓ L.U i)} (hs : s ∈ secOn L (G.hom ⁻¹ᵁ W))
    (z : G₀.left) (i : L.ι) (hzA : G.hom (φ z) ∈ A) (hzW : G.hom (φ z) ∈ W)
    (hz : φ z ∈ G.left.basicOpen (θ i)) :
    ∃ a b : Γ(X, A), IsUnit (gs (φ ≫ G.hom) z A b) ∧
      gs (φ ≫ G.hom) z A b * gs φ z _ (s i) = gs (φ ≫ G.hom) z A a * gs φ z _ (θ i) := by sorry
