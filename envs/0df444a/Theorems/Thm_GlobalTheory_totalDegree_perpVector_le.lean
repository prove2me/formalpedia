-- Prove2me | Theorems.Thm_GlobalTheory_totalDegree_perpVector_le
-- name    : GlobalTheory.totalDegree_perpVector_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:26.579584+00:00
-- url     : https://prove2.me/theorems/62083223-1902-507a-b1ee-9ab401214df1
-- title:
--   Global Theory: total Degree perp Vector le
-- statement:
--   The Global Theory construction uses the total Degree perp Vector le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L197-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L197-L222

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
open MvPolynomial
variable {S τ : Type*} [CommRing S]

theorem GlobalTheory.totalDegree_perpVector_le {p : ℕ} {κ : Type*}
    (ε : Fin p → Module.Dual (MvPolynomial τ S) (κ → MvPolynomial τ S))
    (e' : Fin p → κ → MvPolynomial τ S) (g : κ → MvPolynomial τ S) {d m : ℕ}
    (he : ∀ a a', (ε a (e' a')).totalDegree ≤ d) (hg : ∀ a, (ε a g).totalDegree ≤ d)
    (he' : ∀ a k, (e' a k).totalDegree ≤ m) (hgm : ∀ k, (g k).totalDegree ≤ m) (k : κ) :
    (perpVector ε e' g k).totalDegree ≤ p * d + m := by sorry
