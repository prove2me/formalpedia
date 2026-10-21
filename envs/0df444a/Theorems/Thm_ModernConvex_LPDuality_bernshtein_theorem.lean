-- Prove2me | Theorems.Thm_ModernConvex_LPDuality_bernshtein_theorem
-- name    : ModernConvex.LPDuality.bernshtein_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:31:55.748762+00:00
-- url     : https://prove2.me/theorems/7436a017-2b41-4448-8541-77e82efcb370
-- title:
--   Theorem 1.4.1 — Bernshtein's theorem on trigonometric polynomials: $\|f'\|_\infty \le k\|f\|_\infty$ on $[0, 2\pi]$
-- statement:
--   Let $\Delta = [0, 2\pi]$, let $k \ge 0$ be an integer, and let $f$ be a trigonometric polynomial of degree $\le k$ on $\Delta$,
--   $$f(t) = a_0 + \sum_{l=1}^k \left[a_l\cos(lt) + b_l\sin(lt)\right],$$
--   with real or complex coefficients $a_0, a_1, \dots, a_k, b_1, \dots, b_k$. Then
--   $$\|f'\|_\infty \le k\,\|f\|_\infty,$$
--   where $\|g\|_\infty = \max_{t \in \Delta} |g(t)|$.
--
--   The book uses this inequality to show that the space of trigonometric polynomials of degree $\le k$ on $[0, 2\pi]$ is $k$-regular, which controls how fine a grid must be for a discretized uniform approximation problem to be accurate. The inequality is tight: for $f(t) = \cos(kt)$ it is an equality.
--
--   **Formalization Note** The page prints the polynomial as $a_0 + \sum_{l=1}^k[a_0\cos(lt) + b_0\sin(lt)]$, with the same $a_0, b_0$ in every term. That is a subscript typo: the theorem is stated for "a trigonometric polynomial of degree $\le k$ … with real or complex coefficients", and the page's own tightness example $\cos(kt)$ is not in the printed two-parameter family for $k \ge 2$ (FINDINGS.yaml F1). The Lean states the theorem for general coefficients $a_l, b_l$, given as sequences $a, b : \mathbb N \to \mathbb C$ of which only $a_0, \dots, a_k$ and $b_1, \dots, b_k$ enter; complex coefficients cover the real case. $f : \mathbb R \to \mathbb C$ and $f'$ is the derivative of this function of a real variable, which at the endpoints of $\Delta$ equals the one-sided derivative. The sup-norm inequality is stated in the equivalent form: every bound $M$ on $|f|$ over $\Delta$ gives the bound $kM$ on $|f'|$ over $\Delta$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 31, Theorem 1.4.1 (Bernshtein's theorem on trigonometric polynomials)

import Mathlib

namespace ModernConvex.LPDuality

/-- Ben-Tal–Nemirovski, Theorem 1.4.1 (Bernshtein's theorem on trigonometric polynomials), p. 31:
for a trigonometric polynomial of degree `≤ k` on `Δ = [0, 2π]`,
`f(t) = a₀ + ∑_{l=1}^k [a_l cos(lt) + b_l sin(lt)]` with real or complex coefficients,
`‖f′‖_∞ ≤ k ‖f‖_∞`, stated as "every bound `M` on `|f|` over `Δ` gives the bound `k M` on `|f′|`
over `Δ`". The page prints the coefficients inside the sum as `a₀, b₀`; that is a typo (the
theorem is for every trigonometric polynomial of degree `≤ k`, and the page's own tightness
example `cos(kt)` is outside the printed family), corrected here. -/
theorem bernshtein_theorem (k : ℕ) (a b : ℕ → ℂ) (f : ℝ → ℂ)
    (hf : ∀ t : ℝ, f t = a 0 + ∑ l ∈ Finset.Icc 1 k,
      (a l * (Real.cos (l * t) : ℂ) + b l * (Real.sin (l * t) : ℂ)))
    (M : ℝ) (hM : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖f t‖ ≤ M) :
    ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖deriv f t‖ ≤ k * M := by sorry

end ModernConvex.LPDuality
