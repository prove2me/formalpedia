-- Prove2me | Theorems.Thm_MixedVolFPRAS_Main_proposition_4_4
-- name    : MixedVolFPRAS.Main.proposition_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:31:52.585862+00:00
-- url     : https://prove2.me/theorems/5612f02c-c6f5-4ed8-9c3d-4337a3154f31
-- title:
--   Proposition 4.4 — the (t, λ)-smoothing is the support function of a (λ, 2R/t + λ, 15R/t²)-smooth convex body
-- statement:
--   Let $n\ge2$, $R\ge1$, and let $K\subseteq RB_2^n$ be a convex body. For $0<t\le1/\sqrt n$ and $0<\lambda\le1$, the $(t,\lambda)$-smoothing $\tilde h$ is the support function of a $(\lambda,\Lambda,M)$-smooth convex body $\tilde K$ (Definition 3.2) with
--
--   $$\Lambda=\frac{2R}{t}+\lambda,\qquad M=\frac{15R}{t^2}.$$
--
--   With the choices of Theorem 4.1 this makes $1/\lambda$, $\Lambda$ and $M$ polynomial in $n$, $R$ and $1/\varepsilon$, so Theorem 3.3 applies to the smoothed bodies.
--
--   Differences from the source:
--   - encoding: "$\tilde h$ is the support function of a $(\lambda,\Lambda,M)$-smooth convex body $\tilde K$" → `∃ Kt, supportFunction Kt = smoothing K t lam ∧ IsSmoothBody lam (2R/t + lam) (15R/t²) Kt`; reason: `IsSmoothBody` includes that `Kt` is a convex body; the support function determines it.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 18, Proposition 4.4

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_ConvexGeometry
import Definitions.Def_MixedVolFPRAS_Main_Smoothing
import Definitions.Def_MixedVolFPRAS_Main_Smoothness

open scoped Pointwise

namespace MixedVolFPRAS.Main

/-- **Proposition 4.4.** Let `n ≥ 2`, `R ≥ 1`, `K ⊆ R B₂ⁿ` a convex body, `0 < t ≤ 1/√n`,
`0 < λ ≤ 1`. The `(t, λ)`-smoothing `h̃` is the support function of a `(λ, Λ, M)`-smooth convex
body `K̃` with `Λ = 2R/t + λ`, `M = 15R/t²`. -/
theorem proposition_4_4 {n : ℕ} (hn : 2 ≤ n) (K : Set (E n)) (R t lam : ℝ)
    (hR : 1 ≤ R) (hK : IsConvexBody K) (hKR : K ⊆ R • unitBall n)
    (ht : 0 < t) (ht' : t ≤ 1 / Real.sqrt n) (hlam : 0 < lam) (hlam' : lam ≤ 1) :
    ∃ Kt : Set (E n), supportFunction Kt = smoothing K t lam ∧
      IsSmoothBody lam (2 * R / t + lam) (15 * R / t ^ 2) Kt := by sorry

end MixedVolFPRAS.Main
