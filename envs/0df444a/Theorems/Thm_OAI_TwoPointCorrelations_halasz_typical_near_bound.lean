-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_typical_near_bound
-- name    : OAI.TwoPointCorrelations.halasz_typical_near_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:55.89912+00:00
-- url     : https://prove2.me/theorems/504c548c-18f6-40f7-b139-e432da3d43e5
-- title:
--   From phase-mean renormalization to a mean-square bound for the dyadic polynomial near the origin
-- statement:
--   Let $B:\mathbb N\to\mathbb C$, $N>0$, and reals $C,D\ge0$, $L\ge1$, $M$. Suppose that for every $k\in[N,2N]$, $|\Phi_B(0,k)|\le C(e^{-2M/5}+L^{-1/4})k$, and that for every $u\in[-L^{1/16},L^{1/16}]$ and $k\in[N,2N]$,
--
--   $$\Big|\Phi_B(u,k)-\frac{k^{-iu}}{1-iu}\Phi_B(0,k)\Big|\le DL^{-3/50}k,$$
--
--   where $\Phi_B(u,k)=\sum_{n=1}^kB(n)e^{-iu\log n}$ (`halaszPhaseMean`). Then
--
--   $$\int_{-L^{1/16}}^{L^{1/16}}\big|D_N(u)\big|^2du\le(100\pi C^2+100D^2)\big(e^{-4M/5}+L^{-1/32}\big),$$
--
--   with $D_N(u)=\sum_{N<n\le2N}\frac{B(n)}nn^{-iu}$ (`mrtDyadicPolynomial B N u`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_typical_near_bound`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open MeasureTheory

theorem halasz_typical_near_bound (B : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (C D L M : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hL : 1 ≤ L)
    (hcenter : ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean B 0 k‖ ≤ C*(Real.exp (-2*M/5)+L^(-1/4:ℝ))*k)
    (hnear : ∀ u ∈ Set.Icc (-(L^(1/16:ℝ))) (L^(1/16:ℝ)), ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean B u k-
        (halaszPowerPhase u k/(1+(-u:ℂ)*Complex.I))*halaszPhaseMean B 0 k‖ ≤
          (D*L^(-3/50:ℝ))*k) :
    (∫ u in -(L^(1/16:ℝ))..(L^(1/16:ℝ)), ‖mrtDyadicPolynomial B N u‖^2) ≤
      (100*Real.pi*C^2+100*D^2)*(Real.exp (-4*M/5)+L^(-1/32:ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
