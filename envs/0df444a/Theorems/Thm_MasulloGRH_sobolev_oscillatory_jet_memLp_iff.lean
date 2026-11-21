-- Prove2me | Theorems.Thm_MasulloGRH_sobolev_oscillatory_jet_memLp_iff
-- name    : MasulloGRH.sobolev_oscillatory_jet_memLp_iff
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-21T00:09:48.214238+00:00
-- url     : https://prove2.me/theorems/e3ebb7df-d45d-4d7f-8b07-8fffce5dcaa8
-- title:
--   Weighted L2 threshold for oscillatory logarithmic jets
-- statement:
--   Let $m\in\mathbb N$, $\tau\in\mathbb R$, and $s>1$. For $t>0$, put
--
--   $$\eta_{\tau,m}(t)=e^{i\tau\log t}(\log t)^m.$$
--
--   With $d\mu(t)=dt/t$, the exact weighted $L^2$ condition is
--
--   $$(1+(\log t)^2)^{-s/4}\eta_{\tau,m}(t)\in L^2(\mu)\quad\Longleftrightarrow\quad 2m+1<s.$$
--
--   Thus membership is independent of the oscillation parameter $\tau$, and the endpoint is excluded. This is the positive-real scalar weighted-integrability calculation for the functions in Proposition 9.1.2.5, equations (9.1.2.15)–(9.1.2.16).
--
--   Formalization Note: the measure is the pushforward of Lebesgue measure under the exponential. This statement concerns the displayed weighted function in $L^2$; the abstract negative Sobolev space identification and the general modulated-group compact-fiber reduction are not asserted.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, p. 402, Proposition 9.1.2.5, equations (9.1.2.15)–(9.1.2.16) and the last paragraph of its proof, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. This is the positive-real scalar weighted L2 calculation appearing in that proof, with actual oscillatory jet functions and Haar measure.

import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal

theorem MasulloGRH.sobolev_oscillatory_jet_memLp_iff (m : ℕ) (τ s : ℝ) (hs : 1 < s) :
    MemLp (fun t : ℝ => ((1 + (Real.log t) ^ 2) ^ (-s / 4) : ℝ) •
      (Complex.exp (((τ * Real.log t : ℝ) : ℂ) * Complex.I) * (Real.log t : ℂ) ^ m))
      2 (Measure.map Real.exp volume) ↔ 2 * (m : ℝ) + 1 < s := by sorry
