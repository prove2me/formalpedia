-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_compatible_of_res_eq
-- name    : GlobalTheory.PrimeSection.compatible_of_res_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:28:47.036587+00:00
-- url     : https://prove2.me/theorems/494a7490-2195-45fb-94ca-b876268b88b9
-- title:
--   Prime Section: compatible of res eq
-- statement:
--   The Prime Section construction uses the compatible of res eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L355-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L355-L371

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

theorem GlobalTheory.PrimeSection.compatible_of_res_eq {D : X.Opens} (hD : genericPoint X ∈ D) {r : ∀ a, Γ(X, U a ⊓ D)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ D ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_right)).op (r b))
    (c : Γ(X, D)) {s : ∀ a, Γ(X, U a)}
    (hs : ∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
      X.presheaf.map (homOfLE inf_le_right).op c * r a) (a b : ι) :
    X.presheaf.map (homOfLE inf_le_left).op (s a) =
      g a b * X.presheaf.map (homOfLE inf_le_right).op (s b) := by sorry
