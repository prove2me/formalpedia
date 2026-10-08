-- Prove2me | Theorems.Thm_HessianDamping_IPAHDSC_run_satisfies_eq20
-- name    : HessianDamping.IPAHDSC.run_satisfies_eq20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:42.246981+00:00
-- url     : https://prove2.me/theorems/7287c0e0-7dd8-4b1e-b986-1189eaebee64
-- title:
--   (20), proof of Theorem 9, p. 24 — equivalent second-order form of (IPAHD-SC)
-- statement:
--   Let $f:H\to\mathbb R$ be convex and of class $C^1$ on a real Hilbert space $H$, let $\mu>0$, $s>0$, $\beta\ge0$, and let $(x_k)$ be a run of the inertial proximal algorithm (IPAHD-SC). Then for every $k\ge1$,
--   $$\frac{1}{\sqrt s}(x_{k+1}-2x_k+x_{k-1})+2\sqrt\mu\,(x_{k+1}-x_k)+\beta\big(\nabla f(x_{k+1})-\nabla f(x_k)\big)+\sqrt s\,\nabla f(x_{k+1})=0.$$
--
--   This is the "equivalent formulation" (20) that the proof of Theorem 9 works with: it exhibits the algorithm as an implicit discretization of the inertial dynamic $\ddot x+2\sqrt\mu\dot x+\beta\nabla^2f(x)\dot x+\nabla f(x)=0$.
--
--   **Formalization Note** The run is given through the minimizing property of the proximal step, so the identity is the first-order optimality condition of that step. Positivity of $s$ is implicit on the page ($s=h^2$, $h$ the positive step size).
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 24, proof of Theorem 9, (20)

import Mathlib
import Definitions.Def_HessianDamping_IPAHDSC_Setting

namespace HessianDamping.IPAHDSC

/-- (20), proof of Theorem 9, p. 24: every run of (IPAHD-SC) satisfies, for `k ≥ 1`,
`(1/√s)(x_{k+1} - 2x_k + x_{k-1}) + 2√μ(x_{k+1} - x_k) + β(∇f(x_{k+1}) - ∇f(x_k)) + √s∇f(x_{k+1}) = 0`. -/
theorem run_satisfies_eq20 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfC1 : ContDiff ℝ 1 f)
    (μ : ℝ) (hμ : 0 < μ) (β s : ℝ) (hs : 0 < s) (hβ0 : 0 ≤ β)
    (x : ℕ → H) (hrun : IsIPAHDSCRun f μ β s x) (k : ℕ) (hk : 1 ≤ k) :
    (1 / Real.sqrt s) • (x (k + 1) - (2 : ℝ) • x k + x (k - 1)) +
        (2 * Real.sqrt μ) • (x (k + 1) - x k) +
        β • (gradient f (x (k + 1)) - gradient f (x k)) +
        Real.sqrt s • gradient f (x (k + 1)) = 0 := by sorry

end HessianDamping.IPAHDSC
