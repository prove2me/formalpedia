-- Prove2me | Theorems.Thm_MasulloAudit_kernel_perturbation_prevents_lift_decay
-- name    : MasulloAudit.kernel_perturbation_prevents_lift_decay
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:33:34.962379+00:00
-- url     : https://prove2.me/theorems/561d026d-582f-4c32-874a-a32303edd28a
-- title:
--   The lift norm bounds alone do not force decay after convolution
-- statement:
--   Suppose the representatives have norms between c and C, lie in F, and pair to one with their respective coefficient vectors. If a vector k in the smooth kernel has norm below ε and A k is nonzero, the representatives can be changed in their quotient classes, remaining in F and within the enlarged norm bounds, so that every rank-one trace norm is at least ‖A k‖/C>0. This tests which conclusions follow from the stated lift data. The existence of such a k for a specific convolution is a hypothesis.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen draft of 20 November 2026, Lemma 10.4.2.5 and Terminology 10.4.2.1, pp. 461–462, and the choice of lifts and decay inference (10.4.2.23)–(10.4.2.34), pp. 463–464.

import Definitions.Def_MasulloGRH_HilbertNuclear

open MasulloGRH InnerProductSpace

theorem MasulloAudit.kernel_perturbation_prevents_lift_decay {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K F : Submodule ℂ H) (A : H →L[ℂ] H) (v η : ℕ → H) (k : H)
    (hk : k ∈ K ⊓ F) (hak : A k ≠ 0)
    (c C ε : ℝ) (hC : 0 < C) (hε : ‖k‖ < ε)
    (hv : ∀ i, v i ∈ F ∧ c ≤ ‖v i‖ ∧ ‖v i‖ ≤ C)
    (hbi : ∀ i, inner ℂ (η i) (v i) = 1) :
    0 < ‖A k‖ / C ∧ ∃ w : ℕ → H, ∀ i, w i ∈ F ∧ w i - v i ∈ K ∧
      c-ε < ‖w i‖ ∧ ‖w i‖ < C+ε ∧
      ‖A k‖ / C ≤ traceNorm (rankOne ℂ (A (w i)) (η i)) := by sorry
