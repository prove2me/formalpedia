-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_existsUnique_zpow_mul
-- name    : GlobalTheory.PrimeSection.existsUnique_zpow_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:28:29.678288+00:00
-- url     : https://prove2.me/theorems/16baab07-3896-46d1-ac93-25b49b6de076
-- title:
--   Prime Section: exists Unique zpow mul
-- statement:
--   The Prime Section construction uses the exists Unique zpow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L390-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L390-L455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
variable [IsIntegral X]
variable {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
variable [IsLocallyNoetherian X]
include hη hp

theorem GlobalTheory.PrimeSection.existsUnique_zpow_mul (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    (τ : Γ(X, X.basicOpen t)ˣ)
    (hτ : (τ : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t)
    {r : ∀ a, Γ(X, U a ⊓ X.basicOpen t)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r b))
    (hr0 : ∃ a, r a ≠ 0) :
    ∃! n : ℤ, ∃ s : ∀ a, Γ(X, U a),
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      (∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a) ∧
      ∃ a, ∃ x, x ∉ X.basicOpen t ∧ x ∈ X.basicOpen (s a) := by sorry
