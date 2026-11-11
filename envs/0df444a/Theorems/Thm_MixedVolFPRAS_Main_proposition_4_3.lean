-- Prove2me | Theorems.Thm_MixedVolFPRAS_Main_proposition_4_3
-- name    : MixedVolFPRAS.Main.proposition_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:30:59.798201+00:00
-- url     : https://prove2.me/theorems/a0cdbf66-483d-46e6-8067-0db5cdf39da0
-- title:
--   Proposition 4.3 — the (t, λ)-smoothing is h_{K̃} with K ⊆ K̃ ⊆ K + (Rt√n + λ)B, and ⊆ (1 + ξ)K for t = ξ/(2Rn), λ = ξ/2
-- statement:
--   Let $K\subseteq RB_2^n$ be a convex body, $R>0$, and $t,\lambda>0$. The $(t,\lambda)$-smoothing $\tilde h$ of $h_K$ is the support function of a convex body $\tilde K$ with
--
--   $$K\subseteq\tilde K\subseteq K+(Rt\sqrt n+\lambda)B_2^n .$$
--
--   If moreover $B_2^n\subseteq K$ and $0<\xi\le1/2$, then for $t=\xi/(2Rn)$ and $\lambda=\xi/2$ the corresponding $\tilde K$ satisfies $K\subseteq\tilde K\subseteq(1+\xi)K$.
--
--   The smoothing changes each body by a factor $1+\xi$ only, so the mixed volume of the smoothed bodies approximates the original one (used in Theorem 4.1).
--
--   Differences from the source:
--   - encoding: "$\tilde h$ is the support function of a convex body $\tilde K$" → `∃ Kt, IsConvexBody Kt ∧ supportFunction Kt = smoothing K t lam` (equality on all of $\mathbb{R}^n$); reason: a compact convex set is determined by its support function, so the existential names the paper's $\tilde K$.
--   - encoding: the second sentence → a separate clause, quantified over $\xi$, for the smoothing with $t=\xi/(2Rn)$, $\lambda=\xi/2$; reason: the sentence substitutes these values for $t,\lambda$.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 17, Proposition 4.3

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_ConvexGeometry
import Definitions.Def_MixedVolFPRAS_Main_Smoothing

open scoped Pointwise

namespace MixedVolFPRAS.Main

/-- **Proposition 4.3.** Let `K ⊆ R B₂ⁿ` be a convex body, `R > 0`, `t, λ > 0`. The
`(t, λ)`-smoothing `h̃` is the support function of a convex body `K̃` with
`K ⊆ K̃ ⊆ K + (Rt√n + λ) B₂ⁿ`. If `B₂ⁿ ⊆ K` and `0 < ξ ≤ 1/2`, the choices `t = ξ/(2Rn)`,
`λ = ξ/2` give `K ⊆ K̃ ⊆ (1 + ξ) K`. -/
theorem proposition_4_3 {n : ℕ} (K : Set (E n)) (R t lam : ℝ) (hK : IsConvexBody K)
    (hR : 0 < R) (hKR : K ⊆ R • unitBall n) (ht : 0 < t) (hlam : 0 < lam) :
    (∃ Kt : Set (E n), IsConvexBody Kt ∧ supportFunction Kt = smoothing K t lam ∧
        K ⊆ Kt ∧ Kt ⊆ K + (R * t * Real.sqrt n + lam) • unitBall n) ∧
      (unitBall n ⊆ K → ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 / 2 →
        ∃ Kt : Set (E n), IsConvexBody Kt ∧
          supportFunction Kt = smoothing K (ξ / (2 * R * n)) (ξ / 2) ∧
          K ⊆ Kt ∧ Kt ⊆ (1 + ξ) • K) := by sorry

end MixedVolFPRAS.Main
