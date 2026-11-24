-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedHensel_exists_relation_gradient
-- name    : GlobalTheory.UnramifiedHensel.exists_relation_gradient
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:38.095993+00:00
-- url     : https://prove2.me/theorems/00d0b6cb-ff7e-4d9c-b0b6-b224619c8fe3
-- title:
--   Unramified Hensel: exists relation gradient
-- statement:
--   The Unramified Hensel construction uses the exists relation gradient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRelationGradient.lean#L8-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRelationGradient.lean#L8-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRelationGradient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.UnramifiedHensel

theorem GlobalTheory.UnramifiedHensel.exists_relation_gradient {R A k ι : Type} [CommRing R] [CommRing A] [Field k]
    [Fintype ι] [DecidableEq ι] (ev : MvPolynomial ι R →+* A) (hev : Function.Surjective ev)
    (red : A →+* k) (hred : ∀ c : k, ∃ w : R, red (ev (C w)) = c)
    (h : ∀ φ : A →+* DualNumber k, (∀ a, (φ a).fst = red a) → (∀ w, (φ (ev (C w))).snd = 0) →
      ∀ i, (φ (ev (X i))).snd = 0) (i : ι) :
    ∃ G : MvPolynomial ι R, ev G = 0 ∧
      ∀ j, red (ev (pderiv j G)) = if j = i then 1 else 0 := by sorry
