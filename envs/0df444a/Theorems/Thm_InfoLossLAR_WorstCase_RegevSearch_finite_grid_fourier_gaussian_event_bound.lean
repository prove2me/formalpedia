-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_finite_grid_fourier_gaussian_event_bound
-- name    : InfoLossLAR.WorstCase.RegevSearch.finite_grid_fourier_gaussian_event_bound
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T02:32:55.532235+00:00
-- url     : https://prove2.me/theorems/bfed6074-6364-4b58-a3c7-37fc756fd580
-- title:
--   Finite signed Fourier readout approximates the full coefficient Gaussian
-- statement:
--   Fix a nonsingular integer matrix $B$ in dimension $n\ge1$, a positive width $r$, and a nonzero modulus $M$ satisfying the public cofactor-based grid bound. Let $P_M(T)$ be the squared-amplitude probability of a finite set $T\subset\mathbb Z^n$ after reading each modular coefficient in its centered signed representation. Then
--   $$\left|P_M(T)-\Pr_{z\sim D_{B,r}}[z\in T]\right|\le 4\sqrt{2\,(1/2)^n}+(1/4)^n.$$
--   Here the integer coefficient Gaussian assigns mass proportional to $\exp(-\pi\|Bz\|^2/r^2)$. The conclusion holds for every finite event with a common error bound.
-- source:
--   Finite signed interpretation of Regev, §3.2.2, Lemma 3.14, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, for the target https://prove2.me/theorems/9fdfd0c1-342f-4e71-9410-562b6727463a. The finite-register normalized probabilities, cofactor criterion and explicit truncation and interference estimates specialize that Fourier step.

import Definitions.Def_InfoLossLAR_RegevSearch_FourierGrid
set_option autoImplicit false
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch

theorem finite_grid_fourier_gaussian_event_bound {n M : ℕ} [NeZero M] (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0)
    (r : ℝ) (hr : 0<r) (hn : 0<n) (hM : gridAdequate B r M) (T : Finset (Fin n → ℤ)) :
    |fourierEvent B r M T - ∑ z ∈ T, RegevSketch.coefficientMass B r z| ≤
      4*Real.sqrt (2*(1/2:ℝ)^n)+(1/4:ℝ)^n := by
  sorry

end InfoLossLAR.WorstCase.RegevSearch
