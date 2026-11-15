-- Prove2me | Theorems.Thm_Komlos_bansal_jiang_stronger_beck_fiala
-- name    : Komlos.bansal_jiang_stronger_beck_fiala
-- status  : Open
-- author  : @Himan
-- created : 2026-11-15T02:54:49.462876+00:00
-- url     : https://prove2.me/theorems/5e650329-6020-4f8f-9d37-5066a1bbbd18
-- title:
--   Theorem 5.1 (Stronger Beck–Fiala bound, Bansal–Jiang) — $O(k)$, $O(k^{1/3}\log^{1/3} n)$, $O(k^{1/2})$ by regime of $k$
-- statement:
--   This is the stronger Beck–Fiala bound of Bansal and Jiang, which lists the discrepancy bound in every regime of the column sparsity $k$.
--
--   Let $A \in \{0, \pm 1\}^{m \times n}$ be a matrix in which each column has at most $k$ non-zero entries. Its discrepancy is
--
--   $$
--   \operatorname{disc}(A) = \min_{x \in \{-1,1\}^n} \max_{i \in [m]} \Big| \sum_{j=1}^n A_{ij} x_j \Big| .
--   $$
--
--   Then
--
--   $$
--   \operatorname{disc}(A) =
--   \begin{cases}
--   O(k) & \text{if } k \le \log^{1/2} n, \\
--   O(k^{1/3} \log^{1/3} n) & \text{if } \log^{1/2} n \le k \le \log^2 n, \\
--   O(k^{1/2}) & \text{if } k \ge \log^2 n .
--   \end{cases}
--   $$
--
--   The implied constant is absolute: it does not depend on $k$, $n$, $m$ or $A$, and there are no hidden $\mathrm{poly}(\log\log n)$ factors.
--
--   The third regime is the Beck–Fiala conjecture for $k \ge \log^2 n$ (Theorem 1.3 of the same paper), stated for the larger class of $0/\pm1$ matrices. The second regime improves Banaszczyk's $O(k^{1/2}\log^{1/2} n)$ bound for all $k$ between $\log^{1/2} n$ and $\log^2 n$, and the first regime is the classical $O(k)$ bound of Beck and Fiala. Set systems are the special case of $0/1$ incidence matrices, where $k$ is the maximum number of sets containing one element.
--
--   **Formalization Note** The $O(\cdot)$ is rendered by a single constant $C > 0$ quantified before $k$, $n$, $m$ and $A$, and the three regimes by one case expression that $C$ multiplies. The logarithm is the natural logarithm taken at $n + 2$, as elsewhere in this mission, so that it is positive for every $n$; since the bound is non-decreasing in the logarithm and $\log n \le \log(n+2)$, this does not strengthen the source statement for $n \ge 2$, and for $n \le 1$ every row sum is at most $1$ in absolute value. The two boundary values $k = \log^{1/2}(n+2)$ and $k = \log^2(n+2)$ are assigned to the first and second case respectively; at each boundary the two adjacent expressions agree. The matrix is a function `A : Fin m → Fin n → ℝ` with every entry equal to $0$, $1$ or $-1$, column sparsity counts the rows $i$ with $A_{ij} \ne 0$, and signs are real vectors with entries $\pm 1$ (`IsSignVector`). The case $k = 0$ forces $A = 0$ and the bound $0$. The source also asserts that the colouring is found in polynomial time; only existence is stated here.
-- source:
--   N. Bansal, H. Jiang, Decoupling via affine spectral-independence: Beck-Fiala and Komlos bounds beyond Banaszczyk, 2025, https://arxiv.org/abs/2508.03961 (v2), Section 5, p. 23, Theorem 5.1 (Stronger Beck-Fiala bound)

import Mathlib
import Definitions.Def_Komlos_model

namespace Komlos

theorem bansal_jiang_stronger_beck_fiala :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k n m : ℕ) (A : Fin m → Fin n → ℝ),
        (∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1) →
        (∀ j, ({i | A i j ≠ 0} : Finset (Fin m)).card ≤ k) →
        ∃ ε : Fin n → ℝ, IsSignVector ε ∧
          ∀ i, |∑ j, A i j * ε j| ≤
            C * (if (k : ℝ) ≤ Real.sqrt (Real.log (n + 2)) then (k : ℝ)
                 else if (k : ℝ) ≤ Real.log (n + 2) ^ 2 then
                   (k : ℝ) ^ ((1 : ℝ) / 3) * Real.log (n + 2) ^ ((1 : ℝ) / 3)
                 else Real.sqrt k) := by sorry

end Komlos
