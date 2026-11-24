-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_exists_transport
-- name    : GlobalTheory.PrimeSection.exists_transport
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:44:32.898086+00:00
-- url     : https://prove2.me/theorems/438f63cf-d410-4c22-932d-f62101edc030
-- title:
--   Prime Section: exists transport
-- statement:
--   The Prime Section construction uses the exists transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L67-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L67-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
  [IsIntegral X] [IsLocallyNoetherian X]
  {Y : Scheme.{u}} {j : Y ⟶ X} [IsOpenImmersion j] (hj : j.opensRange = X.basicOpen t)
  {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
  {W : ι → Y.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)
omit [IsIntegral X] [IsLocallyNoetherian X]
include hj

theorem GlobalTheory.PrimeSection.exists_transport (r : ∀ a, Γ(Y, W a))
    (hr : ∀ a b, Y.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        Y.presheaf.map (homOfLE inf_le_right).op (r b))
    (τ : Γ(Y, ⊤)ˣ) (hτ : (τ : Γ(Y, ⊤)) = j.appTop t) :
    ∃ (r' : ∀ a, Γ(X, U a ⊓ X.basicOpen t)) (τ' : Γ(X, X.basicOpen t)ˣ),
      (τ' : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t ∧
      (∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r' a) =
        X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op
          (g a b) * X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r' b)) ∧
      (∀ a, r' a = 0 → r a = 0) ∧ (∀ a, IsUnit (r a) → IsUnit (r' a)) ∧
      ∀ (n : ℤ) (a : ι) (s : Γ(X, U a)), X.presheaf.map (homOfLE inf_le_left).op s =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ' ^ n) : Γ(X, X.basicOpen t)) * r' a ↔
        j.appLE (U a) (W a) (hW a).le s =
          Y.presheaf.map (homOfLE le_top).op (↑(τ ^ n) : Γ(Y, ⊤)) * r a := by sorry
