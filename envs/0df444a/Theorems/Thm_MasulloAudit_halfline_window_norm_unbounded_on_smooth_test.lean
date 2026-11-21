-- Prove2me | Theorems.Thm_MasulloAudit_halfline_window_norm_unbounded_on_smooth_test
-- name    : MasulloAudit.halfline_window_norm_unbounded_on_smooth_test
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T01:36:20.670179+00:00
-- url     : https://prove2.me/theorems/a3d86692-d1d7-4198-8b9f-c526675c0e39
-- title:
--   A smooth compactly supported test has unbounded half-line Sobolev-window norms
-- statement:
--   There exists a real-valued infinitely differentiable function $\varphi$ on $\mathbf R$, with compact support contained in $(2,3)$, for which all the integrands below are integrable on $(0,\infty)$ but the numbers
--   $$Q_n(\varphi)=\left(\int_0^\infty |\varphi(t)|^2\max\{1,t^{2n}\}\,\frac{dt}{t}\right)^{1/2},\qquad n\in\mathbf N,$$
--   are unbounded above: for every $B\in\mathbf R$ there is $n$ such that $B<Q_n(\varphi)$.
--
--   These are exactly the degree-zero expressions for the compact subwindows $[0,n]\subset[0,\infty)$ in (9.2.2.3). Thus their supremum over the half-line cannot give a finite-valued norm on all smooth compactly supported positive-axis tests. The result verifies a concrete finiteness obstruction; it does not assert that every test has infinite supremum, or decide any trace-formula claim.
--
--   Formalization note: smoothness, compact support, positive support, and integrability of every displayed integrand are explicit conclusions. The full Hardy–Sobolev completion is not part of this statement.
-- source:
--   Counterexample to the finiteness implicit in A. M. Masullo, The Music of the Primes, Definition 9.2.2.1, equation (9.2.2.3), and Lemma 9.2.2.2(1),(3), printed pp. 412–413, frozen draft https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . The bump-function obstruction and proposed compact-interval restriction were identified by Yi in Prove2Me mission comment a96ab6a0-9f70-4b3f-ab3e-8c7e38a823f2 (mission 638f9b7f-e232-4624-ba08-5889465bb1e7), referring to https://github.com/mccorvie/riemann-masullo/issues/38#issuecomment-7054381593 . This contribution supplies a Mathlib-only formal proof of that observation, including the positivity and integrability obligations.

import Mathlib

set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem MasulloAudit.halfline_window_norm_unbounded_on_smooth_test :
    ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Ioo 2 3 ∧
      (∀ n : ℕ, IntegrableOn (fun t : ℝ => (φ t)^2 * max 1 (t^(2*n)) / t) (Ioi 0)) ∧
      (∀ B : ℝ, ∃ n : ℕ,
        B < Real.sqrt (∫ t in Ioi (0 : ℝ), (φ t)^2 * max 1 (t^(2*n)) / t)) := by sorry
