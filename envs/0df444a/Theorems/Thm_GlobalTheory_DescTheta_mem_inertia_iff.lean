-- Prove2me | Theorems.Thm_GlobalTheory_DescTheta_mem_inertia_iff
-- name    : GlobalTheory.DescTheta.mem_inertia_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:32:19.655174+00:00
-- url     : https://prove2.me/theorems/ecb42642-ddb4-52a1-9b8d-0b12f9974aff
-- title:
--   Desc Theta: mem inertia iff
-- statement:
--   The Desc Theta construction uses the mem inertia iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSecOnNonvanishingOfTameQuotient.lean#L236-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSecOnNonvanishingOfTameQuotient.lean#L236-L260

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSumSmulSeparatingInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSecOnNonvanishingOfTameQuotient
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
open GlobalTheory GlobalTheory.DescTheta
open GlobalTheory.LB
variable {X Y : Scheme.{0}}

theorem GlobalTheory.DescTheta.mem_inertia_iff {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* Aut X) {W : X.Opens}
    (hW : IsAffineOpen W) (hst : ∀ g, W ≤ (ρ g).hom ⁻¹ᵁ W) (ξ : Sp k ⟶ X) (h : ⊤ ≤ ξ ⁻¹ᵁ W)
    (g : Γ) :
    letI := sectionsAction ρ W hst
    g⁻¹ ∈ (RingHom.ker (evalAt ξ W h)).inertia Γ ↔ ξ ≫ (ρ g).hom = ξ := by sorry
