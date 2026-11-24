-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_germ_eq_mul_germ
-- name    : GlobalTheory.PrimeSection.germ_eq_mul_germ
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:28:52.664462+00:00
-- url     : https://prove2.me/theorems/9b4c69ed-e90f-4367-b27e-453f5e6d7de2
-- title:
--   Prime Section: germ eq mul germ
-- statement:
--   The Prime Section construction uses the germ eq mul germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L342-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L342-L353

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

theorem GlobalTheory.PrimeSection.germ_eq_mul_germ {D : X.Opens} {r : ∀ a, Γ(X, U a ⊓ D)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ D ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_right)).op (r b))
    {a b : ι} {x : X} (ha : x ∈ U a ⊓ D) (hb : x ∈ U b ⊓ D) :
    X.presheaf.germ _ x ha (r a) =
      X.presheaf.germ _ x (show x ∈ U a ⊓ U b from ⟨ha.1, hb.1⟩) (g a b) *
        X.presheaf.germ _ x hb (r b) := by sorry
