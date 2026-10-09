-- Prove2me | Theorems.Thm_HighOrderWalks_TwoSided_theorem_5_9
-- name    : HighOrderWalks.TwoSided.theorem_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:41:52.402848+00:00
-- url     : https://prove2.me/theorems/b60c9187-3820-4c57-b084-f90421daefe2
-- title:
--   Theorem 5.9, p. 22 — Spec(M⁺_k) ⊆ {1} ∪ ⋃_j [(k+1−j)/(k+2) ± (√(k+1)/(k+2))ε_k], eigenvectors near U^j_k
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex that is a two-sided $\lambda$-local spectral expander, with the constants $\varepsilon_k$ of Theorem 5.6. Assume
--   $$\varepsilon_k\le\frac{1}{2\big(1+2(k+1)\sqrt{k+1}\big)}\ \ (0\le k\le n-2)\qquad\text{and}\qquad \varepsilon_{n-1}<\frac{1}{2\sqrt n}.$$
--   Then for every $0\le k\le n-1$:
--   1. the spectrum of the upper random walk $M^+_k$ on $C^k(X,\mathbb R)$ satisfies
--   $$\operatorname{Spec}(M^+_k)\subseteq\{1\}\cup\bigcup_{j=0}^{k}\Big[\frac{k+1-j}{k+2}-\frac{\sqrt{k+1}}{k+2}\varepsilon_k,\ \frac{k+1-j}{k+2}+\frac{\sqrt{k+1}}{k+2}\varepsilon_k\Big];$$
--   2. if $\phi\in C^k_0(X)$ satisfies $M^+_k\phi=\mu\phi$ and $\mu$ lies in the $j$-th interval above, then
--   $$\big\|\phi-P_{U^j_k}\phi\big\|\le\frac{\sqrt{k+1}\,\varepsilon_k}{1-\sqrt{k+1}\,\varepsilon_k}\,\|\phi\| ,$$
--   where $P_{U^j_k}$ is the weighted orthogonal projection onto the subspace $U^j_k$ of §5.3.
--
--   So on a two-sided local spectral expander with small $\lambda$ the spectrum of the $k$-th order walk clusters around the $k+1$ values $\frac{k+1-j}{k+2}$, and each eigenvector lies close to the corresponding space $U^j_k$, which is built from lower-dimensional cochains. This is the structural description of high order random walks that goes beyond the second eigenvalue.
--
--   **Formalization Note.** $\operatorname{Spec}(M^+_k)$ is the set of eigenvalues of $M^+_k$ on the finite-dimensional space $C^k(X,\mathbb R)$, with $M^+_k$ self-adjoint for the weighted inner product; part 1 is stated for every nonzero $\phi$ supported on $X(k)$ (`Supp X (k + 1) φ`) with $M^+_k\phi=\mu\phi$. Requiring the support excludes functions living off the faces, which would otherwise be spurious eigenvectors with eigenvalue $0$. The page leaves $k$ implicit; it is quantified inside the conclusion ($k+1\le n$). $\varepsilon_{n-1}<1/(2\sqrt n)$ is written as `∀ k, k + 1 = n → eps lam k < 1 / (2 * √n)`, avoiding natural-number subtraction. Both hypotheses on $\varepsilon$ make $\sqrt{k+1}\,\varepsilon_k<1/2$, so the denominator in part 2 is positive. $P_{U^j_k}\phi$ is any $u$ with `IsWProj X m (k + 1) (Usp X m k j) φ u`. The constants are those printed on p. 22.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 22, Theorem 5.9

import Mathlib
import Definitions.Def_HighOrderWalks_TwoSided_Setting
import Definitions.Def_HighOrderWalks_TwoSided_Subspaces

namespace HighOrderWalks.TwoSided

/-- Theorem 5.9, p. 22: let `X` be a two-sided `λ`-local spectral expander and `ε_k` as in
`eps`. If `ε_k ≤ 1/(2(1 + 2(k+1)√(k+1)))` for all `0 ≤ k ≤ n - 2` and `ε_{n-1} < 1/(2√n)`,
then for every `0 ≤ k ≤ n - 1`:
1. every eigenvalue `μ` of `M⁺_k` on `C^k(X)` is `1` or lies in
   `[(k+1-j)/(k+2) - (√(k+1)/(k+2)) ε_k, (k+1-j)/(k+2) + (√(k+1)/(k+2)) ε_k]` for some
   `0 ≤ j ≤ k`;
2. if `φ ∈ C^k_0(X)`, `M⁺_k φ = μ φ` and `μ` lies in the `j`-th interval, then
   `‖φ - P_{U^j_k} φ‖ ≤ (√(k+1) ε_k / (1 - √(k+1) ε_k)) ‖φ‖`. -/
theorem theorem_5_9 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : HighOrderWalks.OneSided.IsPureComplex X n) (m : Finset V → ℝ) (hm : HighOrderWalks.OneSided.IsWeight X n m)
    (lam : ℝ) (hexp : TwoSidedLSE X m n lam)
    (hsmall : ∀ k : ℕ, k + 2 ≤ n →
      eps lam k ≤ 1 / (2 * (1 + 2 * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1))))
    (hlast : ∀ k : ℕ, k + 1 = n → eps lam k < 1 / (2 * Real.sqrt (n : ℝ))) :
    ∀ k : ℕ, k + 1 ≤ n →
      (∀ μ : ℝ, ∀ φ : Finset V → ℝ, Supp X (k + 1) φ → φ ≠ 0 → HighOrderWalks.OneSided.upperWalk X m φ = μ • φ →
        μ = 1 ∨ ∃ j ≤ k, |μ - ((k : ℝ) + 1 - (j : ℝ)) / ((k : ℝ) + 2)| ≤
          Real.sqrt ((k : ℝ) + 1) / ((k : ℝ) + 2) * eps lam k) ∧
      (∀ j ≤ k, ∀ μ : ℝ, ∀ φ ∈ C0 X m (k + 1), HighOrderWalks.OneSided.upperWalk X m φ = μ • φ →
        |μ - ((k : ℝ) + 1 - (j : ℝ)) / ((k : ℝ) + 2)| ≤
          Real.sqrt ((k : ℝ) + 1) / ((k : ℝ) + 2) * eps lam k →
        ∀ u : Finset V → ℝ, IsWProj X m (k + 1) (Usp X m k j) φ u →
          HighOrderWalks.OneSided.nrm X m (k + 1) (φ - u) ≤
            Real.sqrt ((k : ℝ) + 1) * eps lam k / (1 - Real.sqrt ((k : ℝ) + 1) * eps lam k) *
              HighOrderWalks.OneSided.nrm X m (k + 1) φ) := by sorry

end HighOrderWalks.TwoSided
