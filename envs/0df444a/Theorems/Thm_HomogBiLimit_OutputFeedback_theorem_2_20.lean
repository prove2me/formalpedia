-- Prove2me | Theorems.Thm_HomogBiLimit_OutputFeedback_theorem_2_20
-- name    : HomogBiLimit.OutputFeedback.theorem_2_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:57.414878+00:00
-- url     : https://prove2.me/theorems/d5c15da1-5161-402c-9038-c6c66c5dcba3
-- title:
--   Theorem 2.20 — converse Lyapunov theorem for vector fields homogeneous in the bi-limit
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^n$ be a vector field homogeneous in the bi-limit with triples $(r_0,\mathfrak d_0,f_0)$ and $(r_\infty,\mathfrak d_\infty,f_\infty)$, and assume the origin is globally asymptotically stable for each of
--   $$\dot x=f(x),\qquad \dot x=f_\infty(x),\qquad \dot x=f_0(x).$$
--   Let $d_{V_0}>\max_i r_{0,i}$ and $d_{V_\infty}>\max_i r_{\infty,i}$. Then there are $C^1$ functions $V,V_0,V_\infty:\mathbb R^n\to\mathbb R$ such that
--
--   1. $V\ge0$ is positive definite and proper;
--   2. for each $i$, $\partial V/\partial x_i$ is homogeneous in the bi-limit with triples $(r_0,\ d_{V_0}-r_{0,i},\ \partial V_0/\partial x_i)$ and $(r_\infty,\ d_{V_\infty}-r_{\infty,i},\ \partial V_\infty/\partial x_i)$;
--   3. $x\mapsto\frac{\partial V}{\partial x}(x)f(x)$, $x\mapsto\frac{\partial V_0}{\partial x}(x)f_0(x)$ and $x\mapsto\frac{\partial V_\infty}{\partial x}(x)f_\infty(x)$ are negative definite.
--
--   This extends Rosier's converse Lyapunov theorem for homogeneous vector fields to homogeneity in the bi-limit; it supplies the Lyapunov functions used for the observer, the state feedback and the output feedback.
--
--   **Formalization Note** Global asymptotic stability (GAS) of the origin of $\dot x=f(x)$ is the published notion `ChitourPrescribedTime.FixedTime.GloballyAsymptoticallyStable` applied to the time-invariant field ($f(0)=0$, from every initial state there is a solution on $[0,\infty)$, Lyapunov stability and uniform global attractivity for *every* solution on $[0,\infty)$; solutions need not be unique, since the fields are only continuous), together with the requirement that no solution escapes to infinity in finite time, so that every solution is defined on $[0,\infty)$. For a continuous autonomous field this is the textbook notion of GAS (Bacciotti–Rosier, *Liapunov Functions and Stability in Control Theory*, §2; uniform attractivity follows from Kurzweil's converse theorem). The paper names $V_0,V_\infty$ only through their partial derivatives; they are quantified existentially as $C^1$ functions, so that the partial derivatives are genuine. $\frac{\partial V}{\partial x}(x)f(x)$ is the Fréchet derivative of $V$ at $x$ applied to $f(x)$.
-- source:
--   Andrieu, Praly, Astolfi, Homogeneous Approximation, Recursive Observer Design, and Output Feedback, arXiv:0903.0298v1, pp. 8–9, Theorem 2.20, (2.7)

import Mathlib
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
import Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems

namespace HomogBiLimit.OutputFeedback

/-- Theorem 2.20 (homogeneous in the bi-limit Lyapunov functions), pp. 8–9. -/
theorem theorem_2_20 {n : ℕ} (f f₀ finf : (Fin n → ℝ) → (Fin n → ℝ))
    (r₀ rinf : Fin n → ℝ) (𝔡₀ 𝔡inf : ℝ)
    (hf : IsHomogBiLimitVF f r₀ 𝔡₀ f₀ rinf 𝔡inf finf)
    (hgas : IsGAS f ∧ IsGAS finf ∧ IsGAS f₀)
    (dVinf dV₀ : ℝ) (hdVinf : ∀ i, rinf i < dVinf) (hdV₀ : ∀ i, r₀ i < dV₀) :
    ∃ V V₀ Vinf : (Fin n → ℝ) → ℝ,
      ContDiff ℝ 1 V ∧ ContDiff ℝ 1 V₀ ∧ ContDiff ℝ 1 Vinf ∧
      (∀ x, 0 ≤ V x) ∧ IsPosDef V ∧ IsProper V ∧
      (∀ i : Fin n, IsHomogBiLimit (partialDeriv V i)
          r₀ (dV₀ - r₀ i) (partialDeriv V₀ i) rinf (dVinf - rinf i) (partialDeriv Vinf i)) ∧
      IsNegDef (fun x => fderiv ℝ V x (f x)) ∧
      IsNegDef (fun x => fderiv ℝ V₀ x (f₀ x)) ∧
      IsNegDef (fun x => fderiv ℝ Vinf x (finf x)) := by sorry

end HomogBiLimit.OutputFeedback
