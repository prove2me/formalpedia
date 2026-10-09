-- Prove2me | Theorems.Thm_IQCAlg_ConvexIQC_lemma_10_general_term
-- name    : IQCAlg.ConvexIQC.lemma_10_general_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:49.36868+00:00
-- url     : https://prove2.me/theorems/a61b4199-6dd5-42ad-92bd-9c8554d894e9
-- title:
--   Proof of Lemma 10, p. 16 — the general term of (3.20) equals (1 − ρ̄²)s_t + ρ̄²p_t ≥ q_t − ρ̄²q_{t−1}
-- statement:
--   Let $f\in S(m,L)$, let $y_\star$ be a point with $\nabla f(y_\star)=0$, and let $0\le\bar\rho\le1$. For a sequence $y$ put $u_k=\nabla f(y_k)$, $\tilde y_k=y_k-y_\star$, $\tilde u_k=u_k-\nabla f(y_\star)$, and let
--   $$s_t:=(\tilde u_t-m\tilde y_t)^{\mathsf T}(L\tilde y_t-\tilde u_t),\qquad p_t:=(\tilde u_t-m\tilde y_t)^{\mathsf T}\big(L(\tilde y_t-\tilde y_{t-1})-(\tilde u_t-\tilde u_{t-1})\big),$$
--   and $q_t=(L-m)g(y_t)-\tfrac12\|\nabla g(y_t)\|^2$ as in (3.16). Then for every $t\ge1$,
--   $$(\tilde u_t-m\tilde y_t)^{\mathsf T}\big(L(\tilde y_t-\bar\rho^2\tilde y_{t-1})-(\tilde u_t-\bar\rho^2\tilde u_{t-1})\big)=(1-\bar\rho^2)s_t+\bar\rho^2p_t$$
--   and
--   $$(\tilde u_t-m\tilde y_t)^{\mathsf T}\big(L(\tilde y_t-\bar\rho^2\tilde y_{t-1})-(\tilde u_t-\bar\rho^2\tilde u_{t-1})\big)\ \ge\ q_t-\bar\rho^2q_{t-1}.$$
--
--   With the weights $\bar\rho^{-2t}$ these lower bounds telescope, which proves the $\bar\rho$-hard form of (3.20).
--
--   **Formalization Note** Stated with $t=k+1$ for $k\ge0$. The page's proof of Lemma 8 uses $g(x)\ge g(y_\star)=0$ and $\nabla g(y_\star)=0$, which hold only when $u_\star=\nabla f(y_\star)=0$; for $u_\star\ne0$ the bound (3.16) behind this inequality is false (at $y_k=y_\star$, $q_k=-\|u_\star\|^2/2$). The hypothesis $\nabla f(y_\star)=0$ is therefore added (it is Lemma 9's hypothesis). Lemmas 8 and 10 themselves are stated for every reference.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 16, proof of Lemma 10, general-term display

import Mathlib
import Definitions.Def_IQCAlg_ConvexIQC_Setting

open scoped InnerProductSpace

namespace IQCAlg.ConvexIQC

/-- Proof of Lemma 10, p. 16: the general term of (3.20) equals `(1 − ρ̄²)s_t + ρ̄²p_t` and is
at least `q_t − ρ̄² q_{t−1}` (here `t = k + 1`), for a reference with `∇f(y⋆) = 0`. -/
theorem lemma_10_general_term {d : ℕ} (f : E d → ℝ) (m L : ℝ) (hf : InSmL f m L) (ys : E d)
    (h0 : gradient f ys = 0) (ρbar : ℝ) (hρbar0 : 0 ≤ ρbar) (hρbar1 : ρbar ≤ 1) :
    ∀ (y : ℕ → E d) (k : ℕ),
      wTerm f m L ρbar y ys k
          = (1 - ρbar ^ 2) * sTerm f m L y ys (k + 1) + ρbar ^ 2 * pTerm f m L y ys k ∧
        qTerm f ys m L (y (k + 1)) - ρbar ^ 2 * qTerm f ys m L (y k)
          ≤ wTerm f m L ρbar y ys k := by sorry

end IQCAlg.ConvexIQC
