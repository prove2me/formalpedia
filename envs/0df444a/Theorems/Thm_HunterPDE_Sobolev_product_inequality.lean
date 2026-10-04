-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_product_inequality
-- name    : HunterPDE.Sobolev.product_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T06:48:25.304989+00:00
-- url     : https://prove2.me/theorems/bd8463b4-b847-4de4-99b7-e60118871c8b
-- title:
--   Theorem 3.27 — Gagliardo / Loomis–Whitney product inequality (3.10)
-- statement:
--   Let $n \ge 2$. For $x = (x_1, \dots, x_n) \in \mathbb{R}^n$ and $1 \le i \le n$ let $x_i' = (x_1, \dots, \hat{x}_i, \dots, x_n) \in \mathbb{R}^{n-1}$ be $x$ with its $i$th coordinate omitted. Suppose $g_1, \dots, g_n \in C_c^\infty(\mathbb{R}^{n-1})$ are nonnegative and define $g(x) = \prod_{i=1}^n g_i(x_i')$. Then
--   $$\int_{\mathbb{R}^n} g \, dx \le \prod_{i=1}^n \|g_i\|_{n-1}, \qquad (3.10)$$
--   where $\|g_i\|_{n-1}$ is the $L^{n-1}(\mathbb{R}^{n-1})$ norm. For $n = 2$ this is Fubini's theorem; in general it estimates the $L^1$ norm of a function of $x$ by the $L^{n-1}$ norms of $n$ functions of the $x_i'$ whose product bounds it. It is the multilinear step in the proof of Theorem 3.28.
--
--   **Formalization Note.** $n$ is written $m + 1$ with $m \ge 1$, so $\mathbb{R}^{n-1}$ is `EuclideanSpace ℝ (Fin m)` without natural-number subtraction; indices are 0-based, `i : Fin (m + 1)`, and $x_i'$ is `Fin.removeNth i` applied to the coordinates of $x$. The left side is the Lebesgue integral of the nonnegative function $g$ in $[0, \infty]$; the norms are `eLpNorm (g i) m`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 61, Theorem 3.27

import Mathlib

open MeasureTheory

namespace HunterPDE.Sobolev

/-- Theorem 3.27 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 61 (Gagliardo / Loomis–Whitney
inequality (3.10)). Write `n = m + 1` with `n ≥ 2` (i.e. `m ≥ 1`). Let `gᵢ ∈ C_c^∞(ℝ^{n−1})`,
`i = 1, …, n` (here `i : Fin (m + 1)`, 0-based), be nonnegative, and let
`g(x) = ∏ᵢ gᵢ(x′ᵢ)`, where `x′ᵢ ∈ ℝ^{n−1}` is `x` with its `i`th coordinate omitted
(`Fin.removeNth i`). Then `∫ g dx ≤ ∏ᵢ ‖gᵢ‖_{n−1}`, the norms being `L^{n−1}(ℝ^{n−1})` norms.
The left side is the Lebesgue integral of the nonnegative function `g`. -/
theorem product_inequality {m : ℕ} (hm : 1 ≤ m)
    (g : Fin (m + 1) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g i))
    (hcpt : ∀ i, HasCompactSupport (g i))
    (hnonneg : ∀ i y, 0 ≤ g i y) :
    ∫⁻ x : EuclideanSpace ℝ (Fin (m + 1)),
        ∏ i, ENNReal.ofReal (g i (WithLp.toLp 2 (Fin.removeNth i (WithLp.ofLp x)))) ≤
      ∏ i, eLpNorm (g i) (m : ENNReal) volume := by sorry

end HunterPDE.Sobolev
