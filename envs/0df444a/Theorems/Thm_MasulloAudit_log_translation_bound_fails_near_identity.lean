-- Prove2me | Theorems.Thm_MasulloAudit_log_translation_bound_fails_near_identity
-- name    : MasulloAudit.log_translation_bound_fails_near_identity
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:24:19.698904+00:00
-- url     : https://prove2.me/theorems/50e52743-495d-44d8-b396-a57f384338a3
-- title:
--   The translation majorant in (9.3.1.6) fails near the identity
-- statement:
--   In logarithmic coordinates t = log |g|, suppose the translation orbit of one nonzero vector is continuous at the identity and has value u there. For s > 0 and every constant C, the operator norm exceeds C max(exp(at),exp(bt)) |t|^(s/2) at all sufficiently small positive t. This checks the printed operator-norm estimate used in the proof of Theorem 10.4.2.8.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen draft, p. 421, Lemma 9.3.1.5, (9.3.1.6), applied on p. 464 immediately before (10.4.2.34).

import Mathlib

open Filter
open scoped Topology

theorem MasulloAudit.log_translation_bound_fails_near_identity {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (U : ℝ → H →L[ℂ] H) (u : H) (hu : u ≠ 0) (hzero : U 0 u = u)
    (hcont : ContinuousAt (fun t => U t u) 0) (a b s C : ℝ) (hs : 0 < s) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      C * max (Real.exp (a*t)) (Real.exp (b*t)) * |t| ^ (s/2) < ‖U t‖ := by sorry
