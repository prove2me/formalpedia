-- Prove2me | Theorems.Thm_ModernConvex_EllipsoidMethod_half_ellipsoid_cover
-- name    : ModernConvex.EllipsoidMethod.half_ellipsoid_cover
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:59.584404+00:00
-- url     : https://prove2.me/theorems/ece9b62e-7816-4bec-8b3d-70cd41b39a35
-- title:
--   (∗) for n > 1 — a half-ellipsoid lies in an ellipsoid of volume ratio ≤ exp{−1/(2n)}
-- statement:
--   Let $n > 1$, let $B$ be an $n\times n$ real matrix with $\operatorname{Det} B \ne 0$, $c \in \mathbb R^n$, and consider the ellipsoid $E = \{x = c + Bu \mid u^Tu \le 1\}$ and, for a vector $a \ne 0$, its half $\widehat E = \{x \in E \mid a^Tx \le a^Tc\}$. Put
--   $$p = \frac{B^Ta}{\sqrt{a^TBB^Ta}},\qquad c^+ = c - \frac{1}{n+1}Bp,\qquad B^+ = \frac{n}{\sqrt{n^2-1}}B + \Big(\frac{n}{n+1} - \frac{n}{\sqrt{n^2-1}}\Big)(Bp)p^T.$$
--   Then:
--
--   1. $B^+ = B\big(\tfrac{n}{\sqrt{n^2-1}}(I_n - pp^T) + \tfrac{n}{n+1}pp^T\big)$;
--   2. $\widehat E \subset E^+ = \{x = c^+ + B^+u \mid u^Tu \le 1\}$;
--   3. the $n$-dimensional volumes satisfy
--   $$\operatorname{Vol}(E^+) = \Big(\frac{n}{\sqrt{n^2-1}}\Big)^{n-1}\frac{n}{n+1}\operatorname{Vol}(E) \le \exp\{-1/(2n)\}\operatorname{Vol}(E).$$
--
--   This is the geometric fact (5.2.13)–(5.2.14) behind every step of the ellipsoid method: the localizer of the solution set shrinks in volume by a factor depending on the dimension only.
--
--   **Formalization Note** Volume is Lebesgue measure on `Fin n → ℝ` (values in $[0,\infty]$, so the identity and the inequality are stated with `ENNReal.ofReal` of the real factors). The book's statement (∗) also has a case $n = 1$, which is false as printed (finding F1); it is the separate item `ModernConvex.EllipsoidMethod.half_segment_cover`.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 344, statement (∗), (5.2.13)–(5.2.14), case n > 1

import Mathlib
import Definitions.Def_ModernConvex_EllipsoidMethod_EllipsoidMethod

open Matrix MeasureTheory

namespace ModernConvex.EllipsoidMethod

/-- Ben-Tal–Nemirovski, p. 344, statement (∗), case `n > 1`, with (5.2.13) and (5.2.14).
Let `E = {x = c + Bu | uᵀu ≤ 1}` with `Det B ≠ 0` and `Ê = {x ∈ E | aᵀx ≤ aᵀc}`, `a ≠ 0`.
With `p = Bᵀa/√(aᵀBBᵀa)`, `c⁺ = c − (1/(n+1))Bp` and
`B⁺ = B((n/√(n²−1))(Iₙ − ppᵀ) + (n/(n+1))ppᵀ) = (n/√(n²−1))B + (n/(n+1) − n/√(n²−1))(Bp)pᵀ`,
the half-ellipsoid `Ê` lies in `E⁺ = {c⁺ + B⁺u | uᵀu ≤ 1}` and
`Vol(E⁺) = (n/√(n²−1))^{n−1} (n/(n+1)) Vol(E) ≤ exp{−1/(2n)} Vol(E)` (Lebesgue measure). -/
theorem half_ellipsoid_cover {n : ℕ} (hn : 1 < n) (c : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (a : Fin n → ℝ) (ha : a ≠ 0) :
    B * (((n : ℝ) / Real.sqrt ((n : ℝ) ^ 2 - 1)) •
          (1 - vecMulVec (cutDirection B a) (cutDirection B a)) +
        ((n : ℝ) / ((n : ℝ) + 1)) • vecMulVec (cutDirection B a) (cutDirection B a)) =
      nextMatrix B a ∧
    halfEllipsoid c B a ⊆ ellipsoid (nextCenter c B a) (nextMatrix B a) ∧
    volume (ellipsoid (nextCenter c B a) (nextMatrix B a)) =
      ENNReal.ofReal (((n : ℝ) / Real.sqrt ((n : ℝ) ^ 2 - 1)) ^ (n - 1) *
        ((n : ℝ) / ((n : ℝ) + 1))) * volume (ellipsoid c B) ∧
    volume (ellipsoid (nextCenter c B a) (nextMatrix B a)) ≤
      ENNReal.ofReal (Real.exp (-1 / (2 * (n : ℝ)))) * volume (ellipsoid c B) := by sorry

end ModernConvex.EllipsoidMethod
