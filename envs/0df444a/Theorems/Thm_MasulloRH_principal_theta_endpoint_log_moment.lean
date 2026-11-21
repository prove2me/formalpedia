-- Prove2me | Theorems.Thm_MasulloRH_principal_theta_endpoint_log_moment
-- name    : MasulloRH.principal_theta_endpoint_log_moment
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T03:33:58.516192+00:00
-- url     : https://prove2.me/theorems/ac4a168a-4f1d-4fdd-a837-406a35aeb8d6
-- title:
--   The endpoint mass of a rational theta sum is its logarithmic input moment with the omitted Euler factors
-- statement:
--   Let $q\ge1$, and let $u:\mathbb R\to\mathbb R$ be twice continuously differentiable, compactly supported, zero on $(-\infty,0]$ and on $[R,\infty)$ for some $R>0$, and of additive mean zero on $(0,\infty)$. Write $\Theta_q u(t)=\sum_{n\ge1,\,(n,q)=1}u(nt)$. Then
--   $$\int_0^\infty\Theta_q u(t)\,dt=\prod_{p\mid q}(1-p^{-1})\int_0^\infty u(x)\log(x)\,dx.$$
--   In particular $q=1$ gives the mass of the full positive rational theta sum. The formal identity uses the principal Dirichlet character modulo $q$ for the coprimality indicator and complex-valued integrals.
-- source:
--   Endpoint specialization of the classical Müntz identity in Jean-François Burnol, “Two complete and minimal systems associated with the zeros of the Riemann zeta function,” J. Théorie des Nombres de Bordeaux 16 (2004), eq. (5), https://ftp5.gwdg.de/pub/EMIS/journals/JTNB/2004-1/Burnol.pdf . Rational theta insertion and omitted factors are described in Masullo, The Music of the Primes, Remark 3.4.2.3. The proof reuses the arithmetic-progression lattice estimates in https://prove2.me/theorems/57a9f371-bd91-4230-a6d7-70870b08b6dc.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.ContDiff.Defs
open Set MeasureTheory

theorem MasulloRH.principal_theta_endpoint_log_moment {q : ℕ} [NeZero q]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ)
    (R : ℝ) (hR : 0 < R) (hvan : ∀ x : ℝ, x ≤ 0 ∨ R ≤ x → ψ x = 0)
    (hmean : (∫ x in Ioi (0:ℝ), ψ x) = 0)
    :
    (∫ t in Ioi (0:ℝ), ∑' n : ℕ,
      (1 : DirichletCharacter ℂ q) (n+1:ℕ) * (ψ (((n:ℝ)+1)*t):ℂ)) =
      (∏ p ∈ q.primeFactors, (1-(p:ℂ)⁻¹)) *
        ∫ t in Ioi (0:ℝ), (Real.log t : ℂ) * (ψ t : ℂ) := by sorry
