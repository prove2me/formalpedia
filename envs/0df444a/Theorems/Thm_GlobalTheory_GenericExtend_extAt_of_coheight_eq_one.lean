-- Prove2me | Theorems.Thm_GlobalTheory_GenericExtend_extAt_of_coheight_eq_one
-- name    : GlobalTheory.GenericExtend.extAt_of_coheight_eq_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:01:23.691543+00:00
-- url     : https://prove2.me/theorems/83deeef2-02a7-43b3-8eed-f6e5db5e5949
-- title:
--   Generic Extend: ext At of coheight eq one
-- statement:
--   The Generic Extend construction uses the ext At of coheight eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleGeneratorExtendingDensePart.lean#L271-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleGeneratorExtendingDensePart.lean#L271-L353

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenericExtend

theorem GlobalTheory.GenericExtend.extAt_of_coheight_eq_one {X U P : Scheme.{0}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (j : U ⟶ X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p] {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {N : LB P}
    (hN : N.IsLB) {eU : U ⟶ pullback p j} (w : eU ≫ pullback.fst p j = j ≫ e)
    (hπ : eU ≫ pullback.snd p j = 𝟙 U)
    {τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N _ τ)
    {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : N.ι),
      e (j (κ z)) ∈ N.U a → gm (κ ≫ eU) z (pullback.fst p j ⁻¹ᵁ N.U a) (τ a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a))
    (y : P) (hx : Order.coheight (p y) = 1) (a : N.ι) (ha : y ∈ N.U a) :
    ExtAt (pullback.fst p j) (N.U a) (τ a).val y ∧
      ExtAt (pullback.fst p j) (N.U a) ((τ a)⁻¹).val y := by sorry
