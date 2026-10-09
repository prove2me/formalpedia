-- Prove2me | Theorems.Thm_IQCAlg_ConvexIQC_eq_3_17
-- name    : IQCAlg.ConvexIQC.eq_3_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:33.805841+00:00
-- url     : https://prove2.me/theorems/488f6097-c954-4b46-bf1d-75bbb05e41b7
-- title:
--   (3.17), proof of Lemma 8, p. 14 — (ũ_k − mỹ_k)ᵀ(Lỹ_k − ũ_k) ≥ q_k when ∇f(y⋆) = 0
-- statement:
--   Let $f\in S(m,L)$ and let $y_\star$ be a point with $\nabla f(y_\star)=0$; let $g$ and $q$ be as in (3.16). For a sequence $y$ put $u_k=\nabla f(y_k)$, $\tilde y_k=y_k-y_\star$, $\tilde u_k=u_k-\nabla f(y_\star)$. Then for every $k\ge0$,
--   $$(\tilde u_k-m\tilde y_k)^{\mathsf T}(L\tilde y_k-\tilde u_k)\ \ge\ (L-m)\,g(y_k)-\frac12\|\nabla g(y_k)\|^2=q_k. \tag{3.17}$$
--
--   The left side is the sector term $s_k$; this bound is used for the first term of (3.15) and, in the proof of Lemma 10, for every term.
--
--   **Formalization Note** The page writes (3.17) at $k=0$; since $y_0$ is arbitrary, it is stated for every $k$ (the proof of Lemma 10 uses it at every $t$). The page's proof of Lemma 8 uses $g(x)\ge g(y_\star)=0$ and $\nabla g(y_\star)=0$, which hold only when $u_\star=\nabla f(y_\star)=0$; for $u_\star\ne0$ this inequality is false (at $y_k=y_\star$, $q_k=-\|u_\star\|^2/2$). The hypothesis $\nabla f(y_\star)=0$ is therefore added (it is Lemma 9's hypothesis). Lemmas 8 and 10 themselves are stated for every reference.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 14, proof of Lemma 8, (3.17)

import Mathlib
import Definitions.Def_IQCAlg_ConvexIQC_Setting

open scoped InnerProductSpace

namespace IQCAlg.ConvexIQC

/-- (3.17), proof of Lemma 8, p. 14: `s_k ≥ q_k`, for a reference with `∇f(y⋆) = 0`. -/
theorem eq_3_17 {d : ℕ} (f : E d → ℝ) (m L : ℝ) (hf : InSmL f m L) (ys : E d)
    (h0 : gradient f ys = 0) :
    ∀ (y : ℕ → E d) (k : ℕ), qTerm f ys m L (y k) ≤ sTerm f m L y ys k := by sorry

end IQCAlg.ConvexIQC
