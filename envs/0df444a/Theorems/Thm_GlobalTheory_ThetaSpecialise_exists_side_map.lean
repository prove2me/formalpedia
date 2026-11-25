-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSpecialise_exists_side_map
-- name    : GlobalTheory.ThetaSpecialise.exists_side_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:35:08.216878+00:00
-- url     : https://prove2.me/theorems/0c1e60fe-1d56-4d8d-9289-d744cdb58116
-- title:
--   Theta Specialise: exists side map
-- statement:
--   The Theta Specialise construction uses the exists side map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PowEqOneOfInjective.lean#L167-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PowEqOneOfInjective.lean#L167-L198

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfInjective
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
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange
variable {S₀ S₁ : Scheme.{0}} {G : Over S₀} [GrpObj G] {A : Over S₁} [GrpObj A]
  {f : S₁ ⟶ S₀} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ) {S F : Type} [CommRing S] [CommRing F]
  {t : Spec (CommRingCat.of F) ⟶ S₁} {t₀ : Spec (CommRingCat.of S) ⟶ S₀} (g : S →+* F)
  (hτ : Spec.map (CommRingCat.ofHom g) ≫ t₀ = t ≫ f) {L₀ : LB G.left} {L₁ : LB A.left}
include hp hτ

theorem GlobalTheory.ThetaSpecialise.exists_side_map (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) (k : ℤ)
    (x : Over.mk t ⟶ A) (θ₀ : ThetaGrp G L₀ k (Over.mk t₀))
    (hx : Spec.map (CommRingCat.ofHom g) ≫ θ₀.pt.left = x.left ≫ φ)
    (π₀ : (Over.mk t₀ ⊗ G).left ⟶ Spec (CommRingCat.of S)) (hπ₀ : π₀ = (fst (Over.mk t₀) G).left)
    (π : (Over.mk t ⊗ A).left ⟶ Spec (CommRingCat.of F)) (hπ : π = (fst (Over.mk t) A).left) :
    ∃ (θ : ThetaGrp A L₁ k (Over.mk t))
      (mv : SecOver π₀ (LPow G L₀ k (Over.mk t₀)) →ₛₗ[g] SecOver π (LPow A L₁ k (Over.mk t))), θ.pt = x ∧
      (∀ s s', IsActOf G L₀ k θ₀ s s' → IsActOf A L₁ k θ (mv s) (mv s')) ∧
      (∀ (s : LB.Sec (LPow G L₀ k (Over.mk t₀)))
        (σ : LB.Sec (LB.LinComb L₀ (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => k))),
        IsPull (φ₁ := fun _ : Fin 1 => (snd (Over.mk t₀) G).left) (snd (Over.mk t₀) G).left s σ →
        PSec w (fun _ : Fin 1 => (snd (Over.mk t) A).left) (fun _ => 𝟙 G.left) (fun _ => k)
          ((snd (Over.mk t) A).left ≫ φ) (mv s) σ) ∧
      (Flat G.hom → ∀ (n : ℕ) (c : Fin n → F), (∀ a : Fin n → S, ∑ i, g (a i) * c i = 0 → ∀ i, a i = 0) →
        ∀ a : Fin n → SecOver π₀ (LPow G L₀ k (Over.mk t₀)), ∑ i, c i • mv (a i) = 0 → ∀ i, a i = 0) := by sorry
