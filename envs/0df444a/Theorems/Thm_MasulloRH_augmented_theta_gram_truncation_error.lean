-- Prove2me | Theorems.Thm_MasulloRH_augmented_theta_gram_truncation_error
-- name    : MasulloRH.augmented_theta_gram_truncation_error
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T16:06:59.059002+00:00
-- url     : https://prove2.me/theorems/d7c8758a-0b11-44b4-b415-c48efbcdb475
-- title:
--   Explicit exterior-integration error for augmented Gaussian theta Gram matrices
-- statement:
--   Let $T,R\ge0$ and $c,b\in\mathbb R$ satisfy $0<c-b$ and $c+b<1$. For real shifts $y_1,\ldots,y_m$, require $|y_i-\log2|\le R$. Use the mission's actual normalized pulse and theta translates,
--
--   $$u_0(x)=\frac{T+1}{\sqrt\pi}e^{-(T+1)^2x^2},\qquad u_i(x)=\theta(x-y_i).$$
--
--   Write $w(x)=e^{2cx+2b|x|}$, and define the exact full and truncated Gram entries
--
--   $$G_{ij}=\int_{\mathbb R}w(x)\overline{u_i(x)}u_j(x)\,dx,\qquad G^{(R)}_{ij}=\int_{-R}^{R}w(x)\overline{u_i(x)}u_j(x)\,dx.$$
--
--   The following explicit amplitudes and decay rates depend only on the finite input parameters. For the pulse column, set
--
--   $$A_0^+=A_0^-=\frac{T+1}{\sqrt\pi}e^{-(T+1)^2R^2},\qquad L_0^+=L_0^-=2(T+1)^2R.$$
--
--   For each theta column, put
--
--   $$\alpha_i=\pi e^{2(R-y_i)},\qquad \beta_i=\frac{\pi}{16}e^{2(R+y_i)},$$
--
--   $$A_i^+=24e^{-\alpha_i},\quad L_i^+=2\alpha_i,\qquad A_i^-=12e^{R+y_i-\beta_i},\quad L_i^-=2\beta_i-1.$$
--
--   Assume that the finitely many displayed tail denominators are positive:
--
--   $$L_i^++L_j^+-2(c+b)>0,\qquad L_i^-+L_j^-+2(c-b)>0.$$
--
--   Then every augmented Gram entry, including pulse–pulse and pulse–theta entries, satisfies
--
--   $$|G_{ij}-G^{(R)}_{ij}|\le\frac{A_i^+A_j^+e^{2(c+b)R}}{L_i^++L_j^+-2(c+b)}+\frac{A_i^-A_j^-e^{-2(c-b)R}}{L_i^-+L_j^-+2(c-b)}.$$
--
--   These are explicit integration-tail estimates for the actual functions. No RH, Mertens, density, or quadrature hypothesis is used. The denominator conditions are finite numerical checks and are retained explicitly, including for the pulse column. The result supplies the outer-tail component of a numerical Gram enclosure; finite-window approximation and quadrature errors must be bounded separately.
--
--   **Formalization Note.** Column zero is the pulse; the remaining columns are represented by `Fin.cons`. The truncated integral uses the closed interval `[-R,R]`; endpoints have Lebesgue measure zero. Integrability of the actual full Gram entries is obtained from the previously proved finite-theta Gram theorem under the stated strip conditions.
-- source:
--   Supporting formalization for the Masullo RH mission. Uses the exact theta reflection theorem https://prove2.me/theorems/8632ce84-3f47-4ac8-b2ff-ae87b3a5a9fe and finite Gaussian-series truncation theorem https://prove2.me/theorems/2e9c99f7-cd06-43f7-a85b-f4d2cc422151 to obtain explicit two-sided envelopes. Actual entry integrability is supplied by MasulloRH.finite_theta_approximation_excludes_rectangle_zeros, https://prove2.me/theorems/8481aa5d-a121-4938-8de2-17c814da37b2 . The new quantitative step is the exponential tangent envelope and exact integration of its discarded rays. This is not claimed to be a new estimate extracted from a particular page of Masullo's paper.

import Definitions.Def_MasulloRH_GaussianThetaApproximation

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ComplexConjugate
open MasulloRH.GaussianApproximation

theorem MasulloRH.augmented_theta_gram_truncation_error
    (m : ℕ) (T c b R : ℝ) (y : Fin m → ℝ)
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hleft : 0 < c-b) (hright : c+b < 1)
    (hshift : ∀ i : Fin m, |y i - Real.log 2| ≤ R) :
    let u : Fin (m+1) → ℝ → ℂ := Fin.cons (pulse T)
      (fun i x => theta (x-y i))
    let Ap : Fin (m+1) → ℝ := Fin.cons
      (((T+1)/Real.sqrt Real.pi) * Real.exp (-(T+1)^2*R^2))
      (fun i => 24 * Real.exp (-Real.pi * (Real.exp (R-y i))^2))
    let Lp : Fin (m+1) → ℝ := Fin.cons (2*(T+1)^2*R)
      (fun i => 2 * Real.pi * (Real.exp (R-y i))^2)
    let Am : Fin (m+1) → ℝ := Fin.cons
      (((T+1)/Real.sqrt Real.pi) * Real.exp (-(T+1)^2*R^2))
      (fun i => 12 * Real.exp (R+y i - (Real.pi/16) * (Real.exp (R+y i))^2))
    let Lm : Fin (m+1) → ℝ := Fin.cons (2*(T+1)^2*R)
      (fun i => 2 * (Real.pi/16) * (Real.exp (R+y i))^2 - 1)
    (∀ i j : Fin (m+1), 0 < Lp i + Lp j - 2*(c+b)) →
    (∀ i j : Fin (m+1), 0 < Lm i + Lm j + 2*(c-b)) →
    ∀ i j : Fin (m+1),
      ‖(∫ x : ℝ, (Real.exp (2*c*x + 2*b*|x|) : ℂ) * conj (u i x) * u j x) -
        ∫ x : ℝ in Icc (-R) R,
          (Real.exp (2*c*x + 2*b*|x|) : ℂ) * conj (u i x) * u j x‖ ≤
        Ap i * Ap j * Real.exp (2*(c+b)*R) / (Lp i + Lp j - 2*(c+b)) +
        Am i * Am j * Real.exp (-2*(c-b)*R) / (Lm i + Lm j + 2*(c-b)) := by sorry
