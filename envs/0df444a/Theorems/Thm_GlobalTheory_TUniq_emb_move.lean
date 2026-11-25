-- Prove2me | Theorems.Thm_GlobalTheory_TUniq_emb_move
-- name    : GlobalTheory.TUniq.emb_move
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:29:19.184807+00:00
-- url     : https://prove2.me/theorems/7123f151-e422-4449-a8fd-aad266afae5d
-- title:
--   TUniq: emb move
-- statement:
--   The TUniq construction uses the emb move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SecCoordOfRatio.lean#L78-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SecCoordOfRatio.lean#L78-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCompatOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordOfRatio
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
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.TUniq
open GlobalTheory.SegreCoord ReciprocityTheory.ChartRestriction.G.Out
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S S' : Scheme.{0}} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem GlobalTheory.TUniq.emb_move {u : TObj g (N' ^ 2) J b s'} {t : TObj g (N' ^ 2) J b s} {f : S' ⟶ S} {φ : u.A.left ⟶ t.A.left}
    (h : MapBy u t f φ) {m : ℕ} (hm : m ∣ N') {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) [IsIso τ]
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) {σ₀} (H : t.Emb m T₀ σ₀) : ∃ σ, u.Emb m T σ ∧
      ∀ (B : Type) [Field B] (y : Sp B ⟶ (T ⊗ u.A).left) (y₀ : Sp B ⟶ (T₀ ⊗ t.A).left),
        y₀ ≫ (fst T₀ t.A).left = y ≫ (fst T u.A).left ≫ τ → y₀ ≫ (snd T₀ t.A).left = y ≫ (snd T u.A).left ≫ φ →
        ∀ w, SecCoord _ σ y w ↔ SecCoord _ σ₀ y₀ w := by sorry
