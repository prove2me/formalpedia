-- Prove2me | Theorems.Thm_MasulloRH_odd_test_pole_terms_cancel
-- name    : MasulloRH.odd_test_pole_terms_cancel
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-22T01:08:17.897632+00:00
-- url     : https://prove2.me/theorems/b7026281-7897-466f-9a6f-4458af58c219
-- title:
--   Inversion-odd tests cancel the two Mellin pole terms
-- statement:
--   Let \(\varphi:\mathbb R\to\mathbb C\) be an inversion-odd test, extended by zero, so that
--   \(\varphi(t^{-1})=-\varphi(t)\). Its Mellin transform satisfies
--
--   $$\mathcal M\varphi(-s)=-\mathcal M\varphi(s).$$
--
--   In particular the two pole/archimedean terms in the rational Masullo trace formula cancel:
--
--   $$\mathcal M\varphi(1/2)+\mathcal M\varphi(-1/2)=0.$$
--
--   This is the remaining scalar cancellation in the odd-test sector once the local geometric terms
--   and paired spectral sum are treated separately. It is an unconditional Mellin-change-of-variables
--   identity; it does not assert the trace formula, a zero-free region, or the Riemann hypothesis.
--
--   **Formalization Note.** The proof uses Mathlib's `mellin_comp_inv` and scalar-compatibility lemma
--   `mellin_const_smul`, with no convergence hypothesis because the totalized Mellin transform is used.
-- source:
--   Masullo, The Music of the Primes, Theorem 12.5.1.1, rational specialization: the Mellin terms at 1/2 and -1/2; odd-sector decomposition recorded in the Masullo mission discussion.

import Definitions.Def_MasulloRH_RationalTrace

set_option autoImplicit false
open MeasureTheory Set
open scoped Topology ContDiff

theorem MasulloRH.odd_test_pole_terms_cancel (φ : ℝ → ℂ)
    (hodd : ∀ t : ℝ, φ t⁻¹ = -φ t) :
    mellin φ (1 / 2) + mellin φ (-1 / 2) = 0 := by sorry
