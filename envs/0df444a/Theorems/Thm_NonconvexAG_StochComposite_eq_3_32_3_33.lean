-- Prove2me | Theorems.Thm_NonconvexAG_StochComposite_eq_3_32_3_33
-- name    : NonconvexAG.StochComposite.eq_3_32_3_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:24:11.023996+00:00
-- url     : https://prove2.me/theorems/2ce96a79-1631-442c-b348-00438a0ac31b
-- title:
--   (3.32)–(3.33) — three-point inequalities for the stochastic prox subproblems (3.26) and (3.27)
-- statement:
--   Let $\mathcal X$ be convex with domain $K$ and prox map $\mathcal P$, and run Algorithm 4 along any realization of the oracle samples, with $\bar\delta_k=\bar G_k-\nabla\Psi(x^{md}_k)$ (so $\nabla\Psi(x^{md}_k)+\bar\delta_k=\bar G_k$). Then for every $k\ge1$ and every $x\in K$,
--   $$\langle\nabla\Psi(x^{md}_k)+\bar\delta_k,x_k-x\rangle+\mathcal X(x_k)\le\mathcal X(x)+\frac1{2\lambda_k}\Big[\|x_{k-1}-x\|^2-\|x_k-x\|^2-\|x_k-x_{k-1}\|^2\Big],$$
--   $$\langle\nabla\Psi(x^{md}_k)+\bar\delta_k,x^{ag}_k-x\rangle+\mathcal X(x^{ag}_k)\le\mathcal X(x)+\frac1{2\beta_k}\Big[\|x^{md}_k-x\|^2-\|x^{ag}_k-x\|^2-\|x^{ag}_k-x^{md}_k\|^2\Big].$$
--
--   These are the optimality conditions of the two prox steps (3.26) and (3.27) in three-point form (Lemma 2 of Ghadimi–Lan–Zhang [11]).
--
--   **Formalization Note** The paper says "for any $x\in\mathbb R^n$"; for $x\notin K$ the right-hand side is $+\infty$ and the inequality is trivial, so it is stated for $x\in K$. The statements are pathwise (for every sample point $\omega$); the gradient map $\nabla\Psi$ enters only through $\bar\delta_k$ and can be arbitrary.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 22, (3.32) and (3.33)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_StochComposite_ProxMap
import Definitions.Def_NonconvexAG_StochComposite_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.StochComposite

open GhadimiLan.RSG (E)
open ConvexOptAlg.SmoothGD

/-- (3.32) and (3.33), p. 22: the three-point inequalities for the prox subproblems (3.26) and
(3.27) of Algorithm 4, with `δ̄ₖ = Ḡₖ − ∇Ψ(x^md_k)` (so `∇Ψ(x^md_k) + δ̄ₖ = Ḡₖ`), for every
realization `ω`, every `k ≥ 1` and every `x` in the domain `K` of `𝒳`. -/
theorem eq_3_32_3_33 {n : ℕ} (gΨ : E n → E n) (K : Set (E n)) (X : E n → ℝ)
    (hX : ConvexOn ℝ K X) (P : E n → E n → ℝ → E n) (hP : IsProxMap K X P)
    {Ξ : Type*} (G : E n → Ξ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (hstep : RSAGStepsizes α β lam m) (x0 : E n)
    {Ω : Type*} (ξ : ℕ → Ω → Ξ) :
    let xk : ℕ → Ω → E n := xSeq G P α β lam m x0 ξ
    let xag : ℕ → Ω → E n := xagSeq G P α β lam m x0 ξ
    let xmd : ℕ → Ω → E n := xmdSeq G P α β lam m x0 ξ
    let δ : ℕ → Ω → E n := deltaBar G gΨ P α β lam m x0 ξ
    ∀ ω : Ω, ∀ k, 1 ≤ k → ∀ x ∈ K,
      inner ℝ (gΨ (xmd k ω) + δ k ω) (xk k ω - x) + X (xk k ω) ≤
          X x + 1 / (2 * lam k) *
            (‖xk (k - 1) ω - x‖ ^ 2 - ‖xk k ω - x‖ ^ 2 - ‖xk k ω - xk (k - 1) ω‖ ^ 2) ∧
        inner ℝ (gΨ (xmd k ω) + δ k ω) (xag k ω - x) + X (xag k ω) ≤
          X x + 1 / (2 * β k) *
            (‖xmd k ω - x‖ ^ 2 - ‖xag k ω - x‖ ^ 2 - ‖xag k ω - xmd k ω‖ ^ 2) := by sorry

end NonconvexAG.StochComposite
