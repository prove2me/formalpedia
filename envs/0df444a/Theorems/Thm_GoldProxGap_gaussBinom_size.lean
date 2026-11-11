-- Prove2me | Theorems.Thm_GoldProxGap_gaussBinom_size
-- name    : GoldProxGap.gaussBinom_size
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:22:03.298734+00:00
-- url     : https://prove2.me/theorems/ac40b964-d0f0-462a-b992-e28d8cae750d
-- title:
--   §3.1, Gaussian binomial coefficients, "Size" — $q^{b(a-b)}\le[a\ b]_q<4q^{b(a-b)}$
-- statement:
--   **Gaussian binomials, size bound (§3.1).** For $0\le b\le a$ the Gaussian binomial coefficient
--   $$
--   \begin{bmatrix}a\\ b\end{bmatrix}_q=\prod_{i=0}^{b-1}\frac{q^{a-i}-1}{q^{b-i}-1}
--   $$
--   satisfies
--   $$
--   q^{b(a-b)}\ \le\ \begin{bmatrix}a\\ b\end{bmatrix}_q\ <\ 4\,q^{b(a-b)} .
--   $$
--   The statement is made for every real $q\ge2$, in particular for every prime power $q$, where $[a\ b]_q$ counts the $b$-dimensional subspaces of $\mathbb F_q^a$.
--
--   The bound converts the Gaussian binomial in the list size $L$ of Theorem 5.1 into the exponent $e_c(\log_2N)^2$ of Corollary 5.2.
--
--   **Formalization Note** $[a\ b]_q$ is the published product formula `HScattered.Hyperplanes.gaussBinom q a b`.
--
--   Differences from the source:
--   - generalization: a prime power q → every real q ≥ 2; reason: the product-formula bound holds for every real q ≥ 2, and every prime power is ≥ 2
--   - reading: "Thus log_q [a b]_q = b(a − b) + O(1), with an absolute constant" → no separate clause; reason: it restates the displayed bound: 0 ≤ log_q [a b]_q − b(a − b) < log_q 4 ≤ 2
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), §3.1, Gaussian binomial coefficients, "Size", p.19

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom

namespace GoldProxGap

/-- **§3.1, Gaussian binomial coefficients, "Size"** (p.19). Dao, Kominers, Thaler, Zheng,
*Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027 submission
manuscript (2 November 2026, sha256 6c2d9ced…): "Let 0 ≤ b ≤ a. Each factor is at least q^{a−b},
and ∏_{j≥1}(1 − q^{−j})^{−1} < 4, so q^{b(a−b)} ≤ [a b]_q < 4 q^{b(a−b)}."

**Formalization Note.** `[a b]_q` is the published product formula
`HScattered.Hyperplanes.gaussBinom q a b` (`∏_{i<b} (1 − q^{a−i}) / ∏_{i<b} (1 − q^{b−i})`, equal
to the paper's `∏_{i<b} (q^{a−i} − 1)/(q^{b−i} − 1)`). The bound is stated for every real
`q ≥ 2`, which contains every prime power. -/
theorem gaussBinom_size (q : ℝ) (hq : 2 ≤ q) (a b : ℕ) (hba : b ≤ a) :
    q ^ (b * (a - b)) ≤ HScattered.Hyperplanes.gaussBinom q a b ∧
      HScattered.Hyperplanes.gaussBinom q a b < 4 * q ^ (b * (a - b)) := by sorry

end GoldProxGap
