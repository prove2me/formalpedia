-- Prove2me | Theorems.Thm_IQCAlg_ConvexIQC_lemma_10
-- name    : IQCAlg.ConvexIQC.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:40.852639+00:00
-- url     : https://prove2.me/theorems/1d341b24-3163-4b6e-ac10-46987c40361c
-- title:
--   Lemma 10 (weighted off-by-one IQC), p. 16 — the quadratic inequality (3.20) for ∇f, f ∈ S(m, L), 0 ≤ ρ̄ ≤ ρ ≤ 1
-- statement:
--   Let $f\in S(m,L)$, that is, $0<m<L$ and $f:\mathbb R^d\to\mathbb R$ is continuously differentiable, strongly convex with parameter $m$, and has an $L$-Lipschitz gradient. Let $(y_\star,u_\star)$ be a reference for the gradient of $f$, i.e. $u_\star=\nabla f(y_\star)$, and let $\phi:=(\nabla f,\nabla f,\dots)$. For a sequence $y=(y_k)_{k\ge0}$ in $\mathbb R^d$ put $u_k=\nabla f(y_k)$, $\tilde y_k:=y_k-y_\star$ and $\tilde u_k:=u_k-u_\star$.
--
--   Then for any $(\bar\rho,\rho)$ with $0\le\bar\rho\le\rho\le1$ and $\rho>0$, every sequence $y$ and every $k\ge0$,
--   $$(\tilde u_0-m\tilde y_0)^{\mathsf T}(L\tilde y_0-\tilde u_0)+\sum_{t=1}^{k}\rho^{-2t}(\tilde u_t-m\tilde y_t)^{\mathsf T}\big(L(\tilde y_t-\bar\rho^2\tilde y_{t-1})-(\tilde u_t-\bar\rho^2\tilde u_{t-1})\big)\ \ge\ 0. \tag{3.20}$$
--
--   This is the quadratic inequality of the weighted off-by-one $\rho$-hard IQC. Fed into the main theorem (Theorem 4) of the paper, it is the constraint that certifies linear convergence rates of first-order methods on $S(m,L)$; $\bar\rho=1$ (with $\rho=1$) recovers the off-by-one IQC (3.15) and $\bar\rho=0$ a weighted sector constraint.
--
--   **Formalization Note** The reference $u_\star=\nabla f(y_\star)$ is arbitrary (not required to vanish). The hypothesis $\rho>0$ is added: the weight $\rho^{-2t}$ is undefined at $\rho=0$, and Lean's convention $0^{-1}=0$ would change the statement there. The weight is written $(\rho^{2t})^{-1}$ and the sum over $t=1,\dots,k$ is indexed by $t+1$ for $t=0,\dots,k-1$. The statement is the lemma's quadratic inequality; the factorization $(\Psi,M)$ is not formalized. It is stated for every sequence $y$ (the page writes $y\in\ell_2^d$).
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 16, Lemma 10, (3.20)

import Mathlib
import Definitions.Def_IQCAlg_ConvexIQC_Setting

open scoped InnerProductSpace

namespace IQCAlg.ConvexIQC

/-- Lemma 10 (weighted off-by-one IQC), p. 16: the quadratic inequality (3.20), for every
reference `u⋆ = ∇f(y⋆)` and every `0 ≤ ρ̄ ≤ ρ ≤ 1` with `ρ > 0`. The sum over `t = 1, …, k` is
indexed by `t + 1` with `t < k`, with weight `ρ^{−2(t+1)}`. -/
theorem lemma_10 {d : ℕ} (f : E d → ℝ) (m L : ℝ) (hf : InSmL f m L) (ys : E d)
    (ρbar ρ : ℝ) (hρbar : 0 ≤ ρbar) (hρbarρ : ρbar ≤ ρ) (hρ1 : ρ ≤ 1) (hρ : 0 < ρ) :
    ∀ (y : ℕ → E d) (k : ℕ),
      0 ≤ sTerm f m L y ys 0
        + ∑ t ∈ Finset.range k, (ρ ^ (2 * (t + 1)))⁻¹ * wTerm f m L ρbar y ys t := by sorry

end IQCAlg.ConvexIQC
