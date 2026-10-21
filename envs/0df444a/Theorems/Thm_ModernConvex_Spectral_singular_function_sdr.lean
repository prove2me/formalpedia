-- Prove2me | Theorems.Thm_ModernConvex_Spectral_singular_function_sdr
-- name    : ModernConvex.Spectral.singular_function_sdr
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:36.877989+00:00
-- url     : https://prove2.me/theorems/156f6721-e984-4e3d-b90e-1245b5e992af
-- title:
--   Proposition 4.2.2 — the SDR (4.2.4) of a symmetric monotone SDr function of the singular values
-- statement:
--   Let $g : \mathbb R^k_+ \to \mathbb R\cup\{+\infty\}$ satisfy the following:
--
--   1. $g$ is symmetric (invariant under permutations of the coordinates);
--   2. $g$ is monotone: $0 \le y \le x$ coordinatewise and $g(x) < +\infty$ imply $g(y) \le g(x)$;
--   3. $g$ is SDr: there is a map $\mathcal S(x,t,u)$ into symmetric matrices, affine in $(x,t,u) \in \mathbb R^k\times\mathbb R\times\mathbb R^K$, with $t \ge g(x) \iff \exists u : \mathcal S(x,t,u) \succeq 0$.
--
--   Let $k \le l$. For a $k\times l$ matrix $X$ let $\sigma_1(X) \ge \cdots \ge \sigma_k(X)$ be its singular values and $\Sigma_j(X) = \sigma_1(X) + \cdots + \sigma_j(X)$. Then $f(X) = g(\sigma(X))$ has the SDR (4.2.4): for every $k\times l$ matrix $X$ and real $t$,
--   $$t \ge f(X) \iff \exists\, x_1,\dots,x_k,\ u:\quad \begin{cases} \mathcal S(x_1,\dots,x_k,t,u) \succeq 0,\\ x_1 \ge x_2 \ge \cdots \ge x_k,\\ \Sigma_j(X) \le x_1 + \cdots + x_j,\quad j = 1,\dots,k.\end{cases}$$
--
--   The result is the singular-value counterpart of Proposition 4.2.1. Compared with the symmetric case, the book adds the monotonicity requirement on $g$. Examples are the Schatten norms of rectangular matrices.
--
--   **Formalization Note** $g$ is defined on $\mathbb R^k_+$ only, so it is extended by $+\infty$ outside $\mathbb R^k_+$: the Lean function is `EReal`-valued on all of $\mathbb R^k$, never $-\infty$, and equals $+\infty$ at every $x$ with a negative entry. The representation by $\mathcal S$ holds for every $x \in \mathbb R^k$, so $\mathcal S(x,t,u) \succeq 0$ forces $x \ge 0$. The page states the monotonicity for $f$ and writes $\operatorname{Dom} f$ and $f(y) \le f(x)$; these are typos for $g$. It also lets the last line run over $j = 1,\dots,m$, a typo for $j = 1,\dots,k$. Both are corrected here. The singular values are written as $\sigma_i(X) = \sqrt{\lambda_i(XX^T)}$, which equals the book's $\lambda_i((XX^T)^{1/2})$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 154, Proposition 4.2.2, Eq. (4.2.4)

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR

open Matrix

namespace ModernConvex.Spectral

/-- Ben-Tal–Nemirovski, Proposition 4.2.2, p. 154: let `g : ℝᵏ₊ → ℝ ∪ {+∞}` be symmetric and
monotone (`0 ≤ y ≤ x ∈ Dom g ⇒ g(y) ≤ g(x)`), extended by `+∞` outside `ℝᵏ₊`, and SDr,
`t ≥ g(x) ⇔ ∃ u : 𝒮(x, t, u) ⪰ 0` with `𝒮` affine in `(x, t, u)`. Then `f(X) = g(σ(X))` on
`k × l` matrices (`k ≤ l`) has the SDR (4.2.4): `t ≥ f(X)` iff there are `x₁, …, x_k, u` with
`𝒮(x, t, u) ⪰ 0`, `x₁ ≥ ⋯ ≥ x_k` and `Σⱼ(X) ≤ x₁ + ⋯ + xⱼ` for `j = 1, …, k`. -/
theorem singular_function_sdr {k l K N : ℕ} (hkl : k ≤ l) (g : (Fin k → ℝ) → EReal)
    (hg : ∀ x, g x ≠ ⊥) (hdom : ∀ x : Fin k → ℝ, ¬ (0 ≤ x) → g x = ⊤)
    (hsym : IsSymmetricFn g)
    (hmono : ∀ x y : Fin k → ℝ, 0 ≤ y → y ≤ x → g x ≠ ⊤ → g y ≤ g x)
    (S : EpiLMI k K N) (hS : S.Represents g) (X : Matrix (Fin k) (Fin l) ℝ) (t : ℝ) :
    g (singVec X) ≤ (t : EReal) ↔
      ∃ (x : Fin k → ℝ) (u : Fin K → ℝ),
        (S.eval x t u).PosSemidef ∧ Antitone x ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ k → sumLargestSing j X ≤ partialSum j x) := by sorry

end ModernConvex.Spectral
