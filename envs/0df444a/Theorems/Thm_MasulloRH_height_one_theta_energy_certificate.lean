-- Prove2me | Theorems.Thm_MasulloRH_height_one_theta_energy_certificate
-- name    : MasulloRH.height_one_theta_energy_certificate
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T16:12:42.945936+00:00
-- url     : https://prove2.me/theorems/89c50384-329f-4aa2-a044-b78a04d6c29a
-- title:
--   An explicit single-translate theta-energy certificate at height one
-- statement:
--   Use the mission's actual dyadic Gaussian theta function
--
--   $$\theta(x)=\sum_{k\in\mathbb Z}\left(e^{-\pi(ke^x)^2}-3e^{-4\pi(ke^x)^2}+2e^{-16\pi(ke^x)^2}\right),$$
--
--   and its normalized pulse at height parameter one,
--
--   $$p_1(x)=\frac{2}{\sqrt\pi}e^{-4x^2}.$$
--
--   The single rational translate
--
--   $$r(x)=p_1(x)-\frac{73}{50}\theta\left(x-\frac34\right)$$
--
--   has integrable weighted squared error and satisfies
--
--   $$\int_{\mathbb R}e^{\frac32x+\frac7{16}|x|}\,|r(x)|^2\,dx<\frac1{64}.$$
--
--   This is one explicit finite-height witness for the Masullo specialization: $n=1$, $\delta=1/32$, $c=3/4$, $b=1/4-\delta=7/32$, with one real rational coefficient and one rational shift. The strict upper bound is $\delta/2$. It imposes no RH, Mertens, density, or unproved numerical assumption. A cofinal family of witnesses at arbitrarily large heights is still required for the mission's RH implication; this statement supplies only the displayed fixed-height instance.
--
--   A related proved height-one certificate, `MasulloRH.height_one_theta_gram_certificate`, uses coefficient $3/2$, weight parameter $b=3/20$, and upper bound $22/1000$. The present witness uses a wider weighted window and the $\delta/2$ margin for the mission's prescribed $n=1$ schedule. It is not a claim that the first finite-height example is new.
--
--   **Formalization Note.** The conclusion explicitly includes integrability, so it does not exploit the totalized value of a nonintegrable Bochner integral. The residual and energy are the exact functions in the published GaussianThetaApproximation definition. There is no replacement theta function or surrogate energy in the conclusion.
-- source:
--   Explicit finite-height supporting formalization for the Masullo RH specialization, using the actual functions in https://prove2.me/definitions/6f34c003-4870-4c6a-b83e-256b289a15db . The rational coefficient 73/50 and shift 3/4 were selected numerically, then verified through a finite certificate of 99 rational integration cells, proved Gaussian truncation and reflection estimates, and analytic bounds on both exterior rays. This is a new computed witness for those definitions, not a theorem attributed to a page of Masullo's draft. Supporting public estimates: https://prove2.me/theorems/2e9c99f7-cd06-43f7-a85b-f4d2cc422151 , https://prove2.me/theorems/8632ce84-3f47-4ac8-b2ff-ae87b3a5a9fe , https://prove2.me/theorems/25b37d57-49aa-48a9-a889-c77a60c8d626 . Related existing finite-height certificate with different coefficient, weight, and margin: https://prove2.me/theorems/d56c0b5b-f1f6-46f1-8968-303a7e716c02 . The proof here was developed independently; the related theorem is not imported.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
open MeasureTheory MasulloRH.GaussianApproximation
set_option autoImplicit false

theorem MasulloRH.height_one_theta_energy_certificate :
    Integrable (fun x : ℝ =>
      Real.exp (2*(3/4)*x + 2*(7/32)*|x|) *
        ‖residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
          (fun _ : Fin 1 => (3/4 : ℝ)) x‖^2) ∧
    energy (3/4) (7/32)
      (residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
        (fun _ : Fin 1 => (3/4 : ℝ))) < (1/64 : ℝ) := by sorry
