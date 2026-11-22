-- Prove2me | Theorems.Thm_MasulloRH_theta_reflected_truncation_error
-- name    : MasulloRH.theta_reflected_truncation_error
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T16:02:18.376307+00:00
-- url     : https://prove2.me/theorems/25b37d57-49aa-48a9-a889-c77a60c8d626
-- title:
--   Explicit error for finite reflected theta evaluation with a rational cutoff
-- statement:
--   Let $\theta$ be the mission's actual dyadic Gaussian theta series. Let $P_K(x)$ be its symmetric finite sum over the nonzero integers from $-K$ to $K$, and use the published rational-cutoff reflected evaluation
--
--   $$\widetilde P_K(x)=\begin{cases}P_K(x),&x\ge-1,\\\frac{e^{-x}}2P_K(-x-\log4),&x<-1.\end{cases}$$
--
--   For every natural $K$ and real $x$,
--
--   $$|\theta(x)-\widetilde P_K(x)|\le24e^{-(K+1)^2/3}\max\{1,e^{-x}/2\}.$$
--
--   Thus, for $x\in[-R,R]$, the error of a shifted evaluation at $x-y$ is at most $24e^{-(K+1)^2/3}\max\{1,e^{R+y}/2\}$. The estimate supplies an explicit finite-evaluation allowance on any compact integration window. It has no RH or Mertens assumption and includes $K=0$.
--
--   **Formalization Note.** The finite functions are defined in `MasulloRH_GaussianThetaTruncation`. The formal conclusion is the pointwise estimate; the displayed compact-window consequence follows by monotonicity of the exponential. The finite reflected expression may jump at its cutoff, so numerical integration should split there.
-- source:
--   Consequence of the proved explicit theta-series tail bound https://prove2.me/theorems/2e9c99f7-cd06-43f7-a85b-f4d2cc422151 and exact Poisson reflection https://prove2.me/theorems/8632ce84-3f47-4ac8-b2ff-ae87b3a5a9fe . Uses the finite-evaluation definition https://prove2.me/definitions/6c5bb9c8-c854-4cd2-b1c2-c90d61a75d82 . This supporting estimate was formalized for rigorous finite-height Gram certificates in the Masullo RH mission.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Definitions.Def_MasulloRH_GaussianThetaTruncation
open MasulloRH.GaussianApproximation
set_option autoImplicit false

theorem MasulloRH.theta_reflected_truncation_error (K : ℕ) (x : ℝ) :
    ‖theta x - thetaPartialReflected K x‖ ≤
      (24 * Real.exp (-((K : ℝ) + 1) ^ 2 / 3)) *
        max 1 (Real.exp (-x) / 2) := by sorry
