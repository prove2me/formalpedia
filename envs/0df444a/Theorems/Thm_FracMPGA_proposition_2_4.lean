-- Prove2me | Theorems.Thm_FracMPGA_proposition_2_4
-- name    : FracMPGA.proposition_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:39:19.926573+00:00
-- url     : https://prove2.me/theorems/8ffbcd31-effa-4757-85dc-7aeeb0fe0675
-- title:
--   Proposition 2.4 — abstract KL convergence framework without lower semicontinuity
-- statement:
--   Let $H:\mathbb R^n\times\mathbb R^m\to(-\infty,+\infty]$ be proper (no lower semicontinuity is assumed), $(a_k)$ a nonnegative sequence, and $(x_k,y_k)$ a bounded sequence such that
--
--   1. (sufficient decrease) there are $C_1>0$, $K_1>0$ with $H(x_{k+1},y_{k+1})+C_1\big(\|x_{k+1}-x_k\|_2^2+a_k\|y_{k+1}-y_k\|_2^2\big)\le H(x_k,y_k)$ for $k\ge K_1$;
--   2. (relative error) there are $C_2>0$, $K_2>0$ such that for each $k\ge K_2$ some $w_{k+1}\in\partial H(x_{k+1},y_{k+1})$ has $\|w_{k+1}\|_2\le C_2\big(\|x_{k+1}-x_k\|_2+\sqrt{a_k}\|y_{k+1}-y_k\|_2\big)$;
--   3. (continuity) $\xi=\lim_kH(x_k,y_k)$ exists and $H\equiv\xi$ on the set $\Upsilon$ of accumulation points of $(x_k,y_k)$.
--
--   If $H$ has the KL property at each point of $\Upsilon$, then
--   $$
--   \sum_{k=0}^\infty\big(\|x_{k+1}-x_k\|_2+\sqrt{a_k}\|y_{k+1}-y_k\|_2\big)<\infty,
--   $$
--   $x_k\to x^\star$ for some $x^\star\in\mathbb R^n$, and $0\in\partial H(x^\star,y^\star)$ for every $(x^\star,y^\star)\in\Upsilon$. Here $\partial$ is the limiting subdifferential.
--
--   The weights $a_k$ let the $y$-part of the decrease degenerate, which is what the lifted fractional objective requires.
--
--   **Formalization Note** The KL property is the published `HasKLProperty` (Definition 1); properness is "some value finite and no value $-\infty$".
--
--   Differences from the source:
--   - encoding: ℝⁿ × ℝᵐ with the Euclidean norm → WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)); reason: Lean convention; the same norm
--   - encoding: H proper with values in (−∞, +∞] → H : … → EReal with some value ≠ ⊤ and no value ⊥; reason: the same functions
--   - encoding: K₁ > 0, K₂ > 0 → natural numbers K with 0 < K; reason: iteration thresholds; equivalent
--   - encoding: Σ (‖x_{k+1} − x_k‖₂ + √a_k‖y_{k+1} − y_k‖₂) < +∞; Υ the accumulation points; ξ = lim H(x_k, y_k) → Summable of the nonnegative terms; MapClusterPt; ξ : ℝ with the limit in EReal; reason: a series of nonnegative terms is finite iff summable; same objects
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §2.2, p.9, Proposition 2.4 (proof in Appendix A, pp.38–39)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
open Filter Topology NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

namespace FracMPGA

/-- **Proposition 2.4** of Zhou, Zhang, Li, arXiv:2311.00957v2, p.9: let
`H : ℝⁿ × ℝᵐ → (−∞, +∞]` be proper, and `{a_k}` a nonnegative scalar sequence. Consider a bounded
sequence `{(x_k, y_k)}` satisfying
(i) (sufficient decrease) there exist `C₁ > 0` and `K₁ > 0` such that
`H(x_{k+1}, y_{k+1}) + C₁(‖x_{k+1} − x_k‖₂² + a_k‖y_{k+1} − y_k‖₂²) ≤ H(x_k, y_k)` for any `k ≥ K₁`;
(ii) (relative error) there exist `C₂ > 0` and `K₂ > 0` such that
`‖w_{k+1}‖₂ ≤ C₂(‖x_{k+1} − x_k‖₂ + √a_k ‖y_{k+1} − y_k‖₂)` holds with some
`w_{k+1} ∈ ∂H(x_{k+1}, y_{k+1})` for any `k ≥ K₂`;
(iii) (continuity) `lim_{k→∞} H(x_k, y_k) = ξ` exists, and `H ≡ ξ` on the set `Υ` of
accumulation points of `{(x_k, y_k)}`.
If `H` satisfies the KL property at each point of `Υ`, then
(i) `Σ_{k=0}^∞ (‖x_{k+1} − x_k‖₂ + √a_k ‖y_{k+1} − y_k‖₂) < +∞`;
(ii) `lim_{k→∞} x_k = x⋆` for some `x⋆ ∈ ℝⁿ`;
(iii) `0 ∈ ∂H(x⋆, y⋆)` for any `(x⋆, y⋆) ∈ Υ`.

**Formalization Note** `H` is a function on the Euclidean product `ℝⁿ × ℝᵐ`
(`WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))`); properness is "some value is
finite and no value is `−∞`". No lower semicontinuity is assumed, as on the page. `∂` is the
limiting subdifferential `LimitingSubdiff` and the KL property is `HasKLProperty` (Definition 1).
`K₁, K₂` are positive natural numbers, `ξ` is real, `Υ` is the set of cluster points
(`MapClusterPt`), and the series in (i), of nonnegative terms, is `Summable`. -/
theorem proposition_2_4 {n m : ℕ}
    (H : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → EReal)
    (hH : (∃ p, H p ≠ ⊤) ∧ ∀ p, H p ≠ ⊥) (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (xs : ℕ → EuclideanSpace ℝ (Fin n)) (ys : ℕ → EuclideanSpace ℝ (Fin m))
    (hbdd : Bornology.IsBounded (Set.range fun k => WithLp.toLp 2 (xs k, ys k)))
    (hdec : ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ K₁ : ℕ, 0 < K₁ ∧ ∀ k ≥ K₁,
      H (WithLp.toLp 2 (xs (k + 1), ys (k + 1))) +
          ((C₁ * (‖xs (k + 1) - xs k‖ ^ 2 + a k * ‖ys (k + 1) - ys k‖ ^ 2) : ℝ) : EReal) ≤
        H (WithLp.toLp 2 (xs k, ys k)))
    (herr : ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ K₂ : ℕ, 0 < K₂ ∧ ∀ k ≥ K₂,
      ∃ w ∈ LimitingSubdiff H (WithLp.toLp 2 (xs (k + 1), ys (k + 1))),
        ‖w‖ ≤ C₂ * (‖xs (k + 1) - xs k‖ + Real.sqrt (a k) * ‖ys (k + 1) - ys k‖))
    (hcont : ∃ ξ : ℝ, Tendsto (fun k => H (WithLp.toLp 2 (xs k, ys k))) atTop (𝓝 (ξ : EReal)) ∧
      ∀ q, MapClusterPt q atTop (fun k => WithLp.toLp 2 (xs k, ys k)) → H q = (ξ : EReal))
    (hKL : ∀ q, MapClusterPt q atTop (fun k => WithLp.toLp 2 (xs k, ys k)) →
      HasKLProperty H q) :
    Summable (fun k => ‖xs (k + 1) - xs k‖ + Real.sqrt (a k) * ‖ys (k + 1) - ys k‖) ∧
    (∃ xstar : EuclideanSpace ℝ (Fin n), Tendsto xs atTop (𝓝 xstar)) ∧
    ∀ q, MapClusterPt q atTop (fun k => WithLp.toLp 2 (xs k, ys k)) →
      (0 : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))) ∈
        LimitingSubdiff H q := by sorry

end FracMPGA
