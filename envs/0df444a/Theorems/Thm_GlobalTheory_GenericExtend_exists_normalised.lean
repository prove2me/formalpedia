-- Prove2me | Theorems.Thm_GlobalTheory_GenericExtend_exists_normalised
-- name    : GlobalTheory.GenericExtend.exists_normalised
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:41.951812+00:00
-- url     : https://prove2.me/theorems/60a2ff5f-149e-43be-94f4-136e41dabba4
-- title:
--   Generic Extend: exists normalised
-- statement:
--   The Generic Extend construction uses the exists normalised property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleGeneratorExtendingDensePart.lean#L178-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleGeneratorExtendingDensePart.lean#L178-L203

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

theorem GlobalTheory.GenericExtend.exists_normalised {X U P Q : Scheme.{0}} {N : LB P} (hN : N.IsLB) {j : U ⟶ X} {e : X ⟶ P}
    {J : Q ⟶ P} {π : Q ⟶ U} {eU : U ⟶ Q} (w : eU ≫ J = j ≫ e) (hπ : eU ≫ π = 𝟙 U)
    {τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N J τ) {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : Compat N e ρ) : ∃ τ', Compat N J τ' ∧ ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : N.ι),
      e (j (κ z)) ∈ N.U a → gm (κ ≫ eU) z (J ⁻¹ᵁ N.U a) (τ' a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a) := by sorry
