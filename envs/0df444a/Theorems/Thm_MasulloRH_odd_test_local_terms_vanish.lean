-- Prove2me | Theorems.Thm_MasulloRH_odd_test_local_terms_vanish
-- name    : MasulloRH.odd_test_local_terms_vanish
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-22T00:59:55.322631+00:00
-- url     : https://prove2.me/theorems/62dc8ed1-38eb-4f1b-b4aa-21466c5b8a5a
-- title:
--   Inversion-odd tests cancel the real and prime-power terms
-- statement:
--   Let \(\varphi:\mathbb R\to\mathbb C\) be the zero-extended form of an inversion-odd test,
--   so that \(\varphi(t^{-1})=-\varphi(t)\) for every real \(t\) (the extension is zero at the
--   non-positive boundary). Then the local terms used in Masullo's rational trace formula vanish
--   pointwise:
--
--   $$
--   (\varphi(t)+\varphi(t^{-1}))\frac{\sqrt t}{t^2-1}=0,
--   \qquad
--   \frac{\log p}{\sqrt{p^{n+1}}}\bigl(\varphi(p^{n+1})+\varphi(p^{-(n+1)})\bigr)=0.
--   $$
--
--   The first identity is the real-place integrand after pairing \(t\) with \(t^{-1}\); the second
--   is each prime-power contribution. This is the geometric half of the inversion-odd sector
--   identified in the discussion of Theorem 12.5.1.1. Combined with the separate spectral cancellation
--   lemma, it reduces the trace formula on odd tests to the remaining pole and measure-convention
--   checks. It does not assert the full trace formula, a zero-free region, or RH.
--
--   **Formalization Note.** `realTraceIntegrand` and `primePowerTraceTerm` are the registered
--   Masullo rational-trace definitions. The hypothesis is stated on the zero-extended real function,
--   so the Lean proof is a pointwise cancellation by the definitions.
-- source:
--   Masullo, The Music of the Primes, Theorem 12.5.1.1, rational specialization: the paired real-place and prime-power terms in the norm-invariant trace calculation; odd-sector decomposition recorded in the Masullo mission discussion.

import Definitions.Def_MasulloRH_RationalTrace

set_option autoImplicit false
open MeasureTheory Set
open scoped Topology ContDiff

theorem MasulloRH.odd_test_local_terms_vanish (φ : ℝ → ℂ)
    (hodd : ∀ t : ℝ, φ t⁻¹ = -φ t) :
    (∀ t : ℝ, realTraceIntegrand φ t = 0) ∧
    (∀ i : Nat.Primes × ℕ, primePowerTraceTerm φ i = 0) := by sorry
