-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_exists_isUnit_appLE_eq
-- name    : GlobalTheory.PrimeSection.exists_isUnit_appLE_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:42:57.892921+00:00
-- url     : https://prove2.me/theorems/e610a833-cb58-4239-aa3f-d23fcfca9737
-- title:
--   Prime Section: exists is Unit app LE eq
-- statement:
--   The Prime Section construction uses the exists is Unit app LE eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L123-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L123-L166

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
include hη hp hj

theorem GlobalTheory.PrimeSection.exists_isUnit_appLE_eq (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    {r : ∀ a, Γ(Y, W a)}
    (hr : ∀ a b, Y.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        Y.presheaf.map (homOfLE inf_le_right).op (r b))
    (hru : ∀ a, IsUnit (r a)) {T T' : Scheme.{u}} [IsIntegral T] [Nonempty T'] (e : T ⟶ X)
    (k : T' ⟶ T) [IsOpenImmersion k] (e' : T' ⟶ Y) (he : e' ≫ j = k ≫ e)
    {y : T} (hy : e y ∉ X.basicOpen t) {a₀ : ι} {A : T.Opens} (hyA : y ∈ A)
    (hA : A ≤ e ⁻¹ᵁ U a₀) {A' : T'.Opens} (hA' : A' = k ⁻¹ᵁ A) (hA'' : A' ≤ e' ⁻¹ᵁ W a₀)
    {u : Γ(T, A)} (hu : IsUnit u) (hur : k.appLE A A' hA'.le u = e'.appLE (W a₀) A' hA'' (r a₀)) :
    ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      ∀ a, j.appLE (U a) (W a) (hW a).le (s a) = r a := by sorry
