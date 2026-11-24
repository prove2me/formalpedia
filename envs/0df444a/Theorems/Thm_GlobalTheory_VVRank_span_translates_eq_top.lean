-- Prove2me | Theorems.Thm_GlobalTheory_VVRank_span_translates_eq_top
-- name    : GlobalTheory.VVRank.span_translates_eq_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:57:40.582607+00:00
-- url     : https://prove2.me/theorems/87d1d1f5-474e-4227-9e59-76d95887ade4
-- title:
--   VVRank: span translates eq top
-- statement:
--   The VVRank construction uses the span translates eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpanEqTopOfFunctionals.lean#L365-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpanEqTopOfFunctionals.lean#L365-L390

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
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
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}

theorem GlobalTheory.VVRank.span_translates_eq_top {k : ℤ} {T : Over S} {I : Type} [Nonempty I]
    (hirr : ∀ W : Submodule Γ(T.left, ⊤) (SecM A L k T),
      (∀ (θ : ThetaGrp A L k T) (s s' : LB.Sec (LPow A L k T)), IsActOf A L k θ s s' →
        SecM.ofSec A s ∈ W → SecM.ofSec A s' ∈ W) → W = ⊥ ∨ W = ⊤)
    (ρ : ThetaGrp A L k T → (SecM A L k T ≃ₗ[Γ(T.left, ⊤)] SecM A L k T))
    (h₁ : ∀ θ s s', IsActOf A L k θ s s' ↔ ρ θ (SecM.ofSec A s) = SecM.ofSec A s')
    (h₃ : ∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v)
    (h₄ : ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v))
    (U : I → ThetaGrp A L k T) (hU : ∀ θ : ThetaGrp A L k T, ∃ c, (U c).pt = θ.pt)
    (v : SecM A L k T) (hv : v ≠ 0) :
    Submodule.span Γ(T.left, ⊤) (Set.range fun c => ρ (U c) v) = ⊤ := by sorry
