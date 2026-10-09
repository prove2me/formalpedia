-- Prove2me | Theorems.Thm_IQCAlg_ConvexIQC_eq_3_18
-- name    : IQCAlg.ConvexIQC.eq_3_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:51.536097+00:00
-- url     : https://prove2.me/theorems/8cb28b60-8b4b-4311-a3d0-47027c77e54e
-- title:
--   (3.18), proof of Lemma 8, p. 14 — the off-by-one term p_t ≥ q_t − q_{t−1} when ∇f(y⋆) = 0
-- statement:
--   Let $f\in S(m,L)$ and let $y_\star$ be a point with $\nabla f(y_\star)=0$; let $q$ be as in (3.16) and $\tilde y,\tilde u$ as in (3.17). Then for every sequence $y$ and every $t\ge1$,
--   $$(\tilde u_t-m\tilde y_t)^{\mathsf T}\big(L(\tilde y_t-\tilde y_{t-1})-(\tilde u_t-\tilde u_{t-1})\big)\ \ge\ q_t-q_{t-1}. \tag{3.18}$$
--
--   Summed over $t$, these bounds telescope; together with (3.16)–(3.17) they prove the off-by-one IQC (Lemma 8).
--
--   **Formalization Note** Stated with $t=k+1$ for $k\ge0$. The page's proof of Lemma 8 uses $g(x)\ge g(y_\star)=0$ and $\nabla g(y_\star)=0$, which hold only when $u_\star=\nabla f(y_\star)=0$; for $u_\star\ne0$ this inequality is false (at $y_k=y_\star$, $q_k=-\|u_\star\|^2/2$). The hypothesis $\nabla f(y_\star)=0$ is therefore added (it is Lemma 9's hypothesis). Lemmas 8 and 10 themselves are stated for every reference.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 14, proof of Lemma 8, (3.18)

import Mathlib
import Definitions.Def_IQCAlg_ConvexIQC_Setting

open scoped InnerProductSpace

namespace IQCAlg.ConvexIQC

/-- (3.18), proof of Lemma 8, p. 14: `p_t ≥ q_t − q_{t−1}` (here `t = k + 1`), for a
reference with `∇f(y⋆) = 0`. -/
theorem eq_3_18 {d : ℕ} (f : E d → ℝ) (m L : ℝ) (hf : InSmL f m L) (ys : E d)
    (h0 : gradient f ys = 0) :
    ∀ (y : ℕ → E d) (k : ℕ),
      qTerm f ys m L (y (k + 1)) - qTerm f ys m L (y k) ≤ pTerm f m L y ys k := by sorry

end IQCAlg.ConvexIQC
