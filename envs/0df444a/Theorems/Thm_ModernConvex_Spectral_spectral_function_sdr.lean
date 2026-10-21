-- Prove2me | Theorems.Thm_ModernConvex_Spectral_spectral_function_sdr
-- name    : ModernConvex.Spectral.spectral_function_sdr
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:32.243015+00:00
-- url     : https://prove2.me/theorems/90657eb6-21cf-411c-bd87-4baf2e0f9d19
-- title:
--   Proposition 4.2.1 — the SDR (4.2.3) of a symmetric SDr function of the eigenvalues
-- statement:
--   Let $g : \mathbb R^m \to \mathbb R\cup\{+\infty\}$ be symmetric, i.e. invariant under permutations of the coordinates $x_1,\dots,x_m$. Assume $g$ is semidefinite representable (SDr): there is a map $\mathcal S(x,t,u)$ with values in symmetric $N\times N$ matrices, affine in $(x,t,u) \in \mathbb R^m\times\mathbb R\times\mathbb R^k$, such that
--   $$t \ge g(x) \iff \exists u : \mathcal S(x,t,u) \succeq 0 .$$
--   For a symmetric $m\times m$ matrix $X$ let $\lambda_1(X) \ge \cdots \ge \lambda_m(X)$ be its eigenvalues and $S_j(X) = \lambda_1(X) + \cdots + \lambda_j(X)$. Then the function $f(X) = g(\lambda(X))$ has the SDR (4.2.3): for every symmetric $X$ and real $t$,
--   $$t \ge f(X) \iff \exists\, x_1,\dots,x_m,\ u:\quad \begin{cases} \mathcal S(x_1,\dots,x_m,t,u) \succeq 0,\\ x_1 \ge x_2 \ge \cdots \ge x_m,\\ S_j(X) \le x_1 + \cdots + x_j,\quad j = 1,\dots,m-1,\\ \operatorname{Tr}(X) = x_1 + \cdots + x_m.\end{cases}$$
--
--   Each $S_j$ is itself SDr (example 18.c). So the right-hand side is the projection of the solution set of a system of linear matrix inequalities, and $f$ is SDr. Examples include $-\operatorname{Det}^q(X)$, $\operatorname{Det}^{-q}(X)$ and the Schatten norms $\|X\|_p = (\sum_i |\lambda_i(X)|^p)^{1/p}$.
--
--   **Formalization Note** $g$ is `EReal`-valued and never $-\infty$. Its convexity, part of the book's definition of an SDr function, is not assumed separately, because it follows from the representation. "$\mathcal S$ affinely depending on $x, t, u$" is an explicit affine map with symmetric coefficient matrices. The conclusion "f is SDr with SDR given by (4.2.3)" is formalized as the equivalence (4.2.3) for every symmetric $X$ and real $t$. The book's following sentence explains why that system is SDr; it is not a separate claim. Indices are 0-based in Lean (`Fin m`), and "$x_1 \ge \cdots \ge x_m$" is `Antitone x`.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 151, Proposition 4.2.1, Eq. (4.2.3)

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR

open Matrix

namespace ModernConvex.Spectral

/-- Ben-Tal–Nemirovski, Proposition 4.2.1, p. 151: let `g : ℝᵐ → ℝ ∪ {+∞}` be symmetric and SDr,
`t ≥ g(x) ⇔ ∃ u : 𝒮(x, t, u) ⪰ 0` with `𝒮` affine in `(x, t, u)`. Then `f(X) = g(λ(X))` on
symmetric `m × m` matrices has the SDR (4.2.3): `t ≥ f(X)` iff there are `x₁, …, x_m, u` with
`𝒮(x, t, u) ⪰ 0`, `x₁ ≥ ⋯ ≥ x_m`, `Sⱼ(X) ≤ x₁ + ⋯ + xⱼ` for `j = 1, …, m − 1`, and
`Tr(X) = x₁ + ⋯ + x_m`. -/
theorem spectral_function_sdr {m k N : ℕ} (g : (Fin m → ℝ) → EReal) (hg : ∀ x, g x ≠ ⊥)
    (hsym : IsSymmetricFn g) (S : EpiLMI m k N) (hS : S.Represents g)
    (X : Matrix (Fin m) (Fin m) ℝ) (hX : X.IsHermitian) (t : ℝ) :
    g (eigVec X) ≤ (t : EReal) ↔
      ∃ (x : Fin m → ℝ) (u : Fin k → ℝ),
        (S.eval x t u).PosSemidef ∧ Antitone x ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → sumLargestEig j X ≤ partialSum j x) ∧
        X.trace = ∑ i, x i := by sorry

end ModernConvex.Spectral
