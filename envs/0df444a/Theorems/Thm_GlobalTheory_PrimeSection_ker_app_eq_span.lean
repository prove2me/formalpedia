-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_ker_app_eq_span
-- name    : GlobalTheory.PrimeSection.ker_app_eq_span
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:42:55.564775+00:00
-- url     : https://prove2.me/theorems/5f44f29e-f6df-4f82-8b52-8c7c783e6231
-- title:
--   Prime Section: ker app eq span
-- statement:
--   The Prime Section construction uses the ker app eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L226-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L226-L242

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

theorem GlobalTheory.PrimeSection.ker_app_eq_span {X Z : Scheme.{u}} {A C : CommRingCat.{u}} {β : A ⟶ C}
    (hβ : Function.Surjective β) {c : A} (hc : RingHom.ker β.hom = Ideal.span {c})
    {f : X ⟶ Spec A} {i : Z ⟶ X} {f' : Z ⟶ Spec C} (h : IsPullback i f' f (Spec.map β))
    {U : X.Opens} (hU : IsAffineOpen U) :
    RingHom.ker (i.app U).hom = Ideal.span {X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (f.appTop ((Scheme.ΓSpecIso A).inv c))} := by sorry
