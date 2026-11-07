-- Prove2me | Theorems.Thm_MCPoise_theorem_C_1
-- name    : MCPoise.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:36:30.375073+00:00
-- url     : https://prove2.me/theorems/4464ace7-7bd4-4c78-acfb-d0156b2715a2
-- title:
--   Theorem C.1 (matrix rounding) — integral $\bar y$ with $(A\bar y)_a < (Ay)_a + d$
-- statement:
--   Let $A$ be a real matrix and $y$ a real vector. Suppose that in every column of $A$ the sum of the positive entries is at most $d$ and the sum of the negative entries is at least $-d$, where $d > 0$.
--
--   **Theorem C.1.** There is an integral vector $\bar y$ with $\bar y_q \in \{\lfloor y_q \rfloor, \lceil y_q \rceil\}$ for every coordinate $q$, and
--   $$(A \bar y)_a < (A y)_a + d$$
--   for every row $a$. A polynomial-time algorithm finds it on rational data.
--
--   Differences from the source:
--   - reading: a polynomial-time algorithm on a real matrix and vector → existence for real data, and one machine on rational data; reason: time on real input has no meaning on a Turing machine; the use in Lemma 2.11 is rational
--   - reading: an efficient, polynomial-time algorithm → one deterministic machine `Turing.TM2ComputableInPolyTime`, polynomial in a fixed binary encoding on every input; reason: the source names no machine, and every step it describes is deterministic
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem C.1, p.36

import Mathlib
import Definitions.Def_MCPoise_MatIn

namespace MCPoise

/-- **Theorem C.1 (matrix rounding).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem C.1, p.36: "Let A be a real matrix and let y be a real vector. Suppose that, in every column of A, the sum of the positive entries is at most d and the
sum of the negative entries is at least −d, where d > 0. There is a polynomial-time algorithm that finds an integral vector ȳ such that ȳ_q ∈ {⌊y_q⌋, ⌈y_q⌉} for every
coordinate q, and (Aȳ)_a < (Ay)_a + d for every row a."

First clause: the vector `ȳ` exists for real data. Second clause: one Turing machine finds it on rational data.

**Formalization Note.** Time on real input has no meaning for a Turing machine, so the algorithm is stated on rational data with encoded input. -/
theorem theorem_C_1 :
    (∀ {m N : ℕ} (A : Matrix (Fin m) (Fin N) ℝ) (y : Fin N → ℝ) (d : ℝ), 0 < d →
      (∀ q, ∑ a, max (A a q) 0 ≤ d) → (∀ q, -d ≤ ∑ a, min (A a q) 0) →
      ∃ ybar : Fin N → ℤ, (∀ q, ybar q = ⌊y q⌋ ∨ ybar q = ⌈y q⌉) ∧
        ∀ a, A.mulVec (fun q => (ybar q : ℝ)) a < A.mulVec y a + d) ∧
    ∃ alg : MatIn → List ℤ, Nonempty (Turing.TM2ComputableInPolyTime encMatIn encInts alg) ∧
      ∀ R : MatIn, (∀ row ∈ R.A, row.length = R.y.length) → 0 < R.d →
        (∀ q, ∑ a, max (R.mat a q) 0 ≤ (R.d : ℝ)) → (∀ q, -(R.d : ℝ) ≤ ∑ a, min (R.mat a q) 0) →
        (alg R).length = R.y.length ∧
        (∀ q : Fin R.y.length, (alg R).getD q.val 0 = ⌊R.y.get q⌋ ∨ (alg R).getD q.val 0 = ⌈R.y.get q⌉) ∧
        ∀ a, R.mat.mulVec (fun q => (((alg R).getD q.val 0 : ℤ) : ℝ)) a <
          R.mat.mulVec (fun q => ((R.y.get q : ℚ) : ℝ)) a + (R.d : ℝ) := by sorry

end MCPoise
