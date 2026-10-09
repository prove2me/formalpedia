-- Prove2me | Theorems.Thm_IQCAlg_ConvexIQC_lemma_8
-- name    : IQCAlg.ConvexIQC.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:08.581752+00:00
-- url     : https://prove2.me/theorems/f7607547-e2d3-4f12-916c-08a78da4436f
-- title:
--   Lemma 8 (off-by-one IQC), pp. 13–14 — the quadratic inequality (3.15) for ∇f, f ∈ S(m, L)
-- statement:
--   Let $f\in S(m,L)$ and let $(y_\star,u_\star)$ be a reference for the gradient of $f$, i.e. $u_\star=\nabla f(y_\star)$. Let $\phi:=(\nabla f,\nabla f,\dots)$. For a sequence $y=(y_k)_{k\ge0}$ in $\mathbb R^d$ put $u_k=\nabla f(y_k)$, $\tilde y_k:=y_k-y_\star$ and $\tilde u_k:=u_k-u_\star$. Then for every sequence $y$ and every $k\ge0$,
--   $$(\tilde u_0-m\tilde y_0)^{\mathsf T}(L\tilde y_0-\tilde u_0)+\sum_{t=1}^{k}(\tilde u_t-m\tilde y_t)^{\mathsf T}\big(L(\tilde y_t-\tilde y_{t-1})-(\tilde u_t-\tilde u_{t-1})\big)\ \ge\ 0. \tag{3.15}$$
--
--   This is the quadratic inequality of the off-by-one hard IQC; the case $k=0$ is the sector inequality.
--
--   **Formalization Note** The reference $u_\star=\nabla f(y_\star)$ is arbitrary (not required to vanish). The sum over $t=1,\dots,k$ is indexed by $t+1$ for $t=0,\dots,k-1$. The statement is the lemma's quadratic inequality; the factorization $(\Psi,M)$ is not formalized. It is stated for every sequence $y$ (the page writes $y\in\ell_2^d$).
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, pp. 13–14, Lemma 8, (3.15)

import Mathlib
import Definitions.Def_IQCAlg_ConvexIQC_Setting

open scoped InnerProductSpace

namespace IQCAlg.ConvexIQC

/-- Lemma 8 (off-by-one IQC), pp. 13–14: the quadratic inequality (3.15), for every
reference `u⋆ = ∇f(y⋆)`. The sum over `t = 1, …, k` is indexed by `t + 1` with `t < k`. -/
theorem lemma_8 {d : ℕ} (f : E d → ℝ) (m L : ℝ) (hf : InSmL f m L) (ys : E d) :
    ∀ (y : ℕ → E d) (k : ℕ),
      0 ≤ sTerm f m L y ys 0 + ∑ t ∈ Finset.range k, pTerm f m L y ys t := by sorry

end IQCAlg.ConvexIQC
