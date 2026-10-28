-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_fderiv_logLaplace_jointLaw_none_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.fderiv_logLaplace_jointLaw_none_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:25.251994+00:00
-- url     : https://prove2.me/theorems/c111409b-45db-45b0-903a-b9f1a6b86e12
-- title:
--   Local Scalar-Direction Fréchet Derivative of the Suspension Log-Laplace Transform
-- statement:
--   This auxiliary statement formalizes equation (111) in the suspension argument for Proposition 7.1, p. 28, of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $n,N\in\mathbb N$ with $N>0$, and $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`). Let $h_V:$ `RegularPotential` $V\ a\ b'$: $a,b'>0$, $V$ is smooth with derivatives of polynomial growth, and $a\operatorname{Id}\le D^2V\le b'\operatorname{Id}$. Put $\mu=h_V.\text{law}$, the normalized $e^{-V}$ law. Assume:
--   1. $\beta>0$ and $f:E\to\mathbb R$ is $C^2$.
--   2. $\|D(Df)(x)\|\le M$ for every $x$, where $M\in\mathbb R$.
--   3. $(\beta/\sqrt N)M\le a$.
--
--   Set $\sigma_\beta=\sqrt{1+2/\beta^2}$ (`sigma`) and $\lambda=$ `jointLaw` $\mu\ f\ \beta\ \sigma_\beta\ N$ on $H=$ `JointSpace` $N\ n$. Write $z_0$ for the scalar coordinate, $z_i$ for the copy blocks, and $e_0$ for the scalar unit vector. There exists $r>0$ such that every $z\in H$ with $\|z\|<r$ and $z_0=0$ satisfies
--   $$
--   D\Lambda_\lambda(z)[e_0]=\frac{1}{\sigma_\beta\sqrt N}\sum_{i\in\operatorname{Fin}N}F_f(z_i).
--   $$
--
--   Here $D$ is `fderiv`, $\Lambda_\lambda=$ `logLaplace`, and $F_f=$ `tiltAverage`. This supplies the local first-derivative identity for mixed-cumulant calculations; it does not require isotropy or normalization of $f$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem fderiv_logLaplace_jointLaw_none {n N : ℕ} (hN : 0 < N) (V : EuclideanSpace ℝ (Fin n) → ℝ)
--       {a b' : ℝ} (hV : KLS.RegularPotential V a b') {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ}
--       (hβ : 0 < β) (hf : ContDiff ℝ 2 f) (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
--       (h110 : β / Real.sqrt N * M ≤ a) :
--       ∃ r > 0, ∀ z : JointSpace N n, ‖z‖ < r → z none = 0 →
--         fderiv ℝ (logLaplace (jointLaw (hV.law : Measure _) f β (sigma β) N)) z
--             (EuclideanSpace.single none 1) =
--           (sigma β * Real.sqrt N)⁻¹ *
--             ∑ i, tiltAverage (hV.law : Measure _) f (WithLp.toLp 2 fun j => z (some (i, j)))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Derivatives`](https://prove2.me/theorems/3fa39843-9f8d-446f-806f-25b47f8ada2b).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Selected supporting theorems: [`contDiffOn_logLaplace_ball`](https://prove2.me/theorems/dd1e2494-e9a9-46a2-a434-95c8dca4c3ef), [`convexOn_of_hessian_ge`](https://prove2.me/theorems/dc198aa0-40e7-4ce6-bf96-9622594c954d), [`exists_integrable_exp_norm`](https://prove2.me/theorems/cae54259-25c9-4b6d-b8ab-140080dd2348), [`exists_f_abs_exponential_moment`](https://prove2.me/theorems/fe683760-0019-4c41-91b0-97d1cf8c50c3), [`exists_graph_norm_moment_of_local_moments`](https://prove2.me/theorems/8a8ce263-41ce-4c1c-a341-699721b9b1dc).
--
--   Previous: [`joint_first_derivative_of_radii`](https://prove2.me/theorems/36ffa587-610d-4253-bdcc-464589c23e0b) · Next: [`source_mixed_cumulant_entries`](https://prove2.me/theorems/64ef58a4-ed4b-40d5-9f37-7e5aad5551d2).
--
--   [Source excerpt, lines 360–368](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Derivatives.lean#L360-L368) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Derivatives.lean#L359-L393 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Derivatives`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.fderiv_logLaplace_jointLaw_none`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Derivatives

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery

theorem FunctionalInequalities.KLS.LogConcave.Suspension.fderiv_logLaplace_jointLaw_none_readable {n N : ℕ} (hN : 0 < N) (V : EuclideanSpace ℝ (Fin n) → ℝ)
    {a b' : ℝ} (hV : KLS.RegularPotential V a b') {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ}
    (hβ : 0 < β) (hf : ContDiff ℝ 2 f) (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (h110 : β / Real.sqrt N * M ≤ a) :
    ∃ r > 0, ∀ z : JointSpace N n, ‖z‖ < r → z none = 0 →
      fderiv ℝ (logLaplace (jointLaw (hV.law : Measure _) f β (sigma β) N)) z
          (EuclideanSpace.single none 1) =
        (sigma β * Real.sqrt N)⁻¹ *
          ∑ i, tiltAverage (hV.law : Measure _) f (WithLp.toLp 2 fun j => z (some (i, j))) := by sorry
