-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_3_20
-- name    : GeoQAC.Supplement.theorem_3_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:24:44.343506+00:00
-- url     : https://prove2.me/theorems/04c67c56-cd7d-47ed-9304-ddf8bf3e7379
-- title:
--   Theorem 3.20 — width reduction for polynomial-size clean PARITY families
-- statement:
--   Let $c\ge1$ and $A$ be constants, and let $(C_n)$ be a QAC family (no geometric restriction): $C_n$ has depth $d(n)$, at most $A n^c$ qubits and at most $A n^c$ gates, and is an exact clean implementation of the parity unitary $U_{\oplus n}$, for every $n\ge2$. Then there are constants $B>0$ and $e$, independent of $n$ and $r$, such that for every $n\ge2$ and every integer $r$ with $1\le r\le\lfloor\log_2 n\rfloor$ there is a $[w,h]$-2D-QAC circuit that is an exact clean implementation of $U_{\oplus n}$ with
--   $$
--   w\le B\,r\,n^{c/r},\qquad h\le B\,2^r n^{1+(c-1)/r},\qquad \text{depth}\le B\,r\,d\big(\lceil n^{1/r}\rceil\big),
--   $$
--   and at most $B n^e$ gates.
--
--   Any polynomial-size clean parity family can thus be laid out on a grid of width $n^{O(1/r)}$ at the cost of a factor $r$ in depth.
--
--   Differences from the source:
--   - generalization: the family computes exact clean PARITY_n with O(n^c) qubits and gates (all n) → the hypotheses are assumed only for n ≥ 2; reason: the construction calls the family only at block sizes ⌈n^{1/r}⌉ ≥ 2, and a family satisfying the source's hypotheses satisfies these
--   - encoding: 1 ≤ r ≤ ⌊log₂ n⌋; polynomial-size → 1 ≤ r ∧ 2^r ≤ n; gate count ≤ B n^e (the qubit count is bounded by w·h); reason: same conditions
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 3.20, p.27

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_IsCleanImpl
import Definitions.Def_GeoQAC_Supplement_gateCount

namespace GeoQAC.Supplement

open GeoQAC

/-- **Theorem 3.20** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.27). "For a constant
`c ≥ 1`, suppose a QAC family computes exact clean `PARITY_n` with depth `d(n)` and `O(n^c)` qubits
and gates. For every `n ≥ 2` and integer `1 ≤ r ≤ ⌊log₂ n⌋`, there is a polynomial-size
`[O(r n^{c/r}), O(2^r n^{1+(c−1)/r})]`-2D-QAC circuit that computes exact clean `PARITY_n` with depth
`O(r d(⌈n^{1/r}⌉))`. The implicit constants are independent of `n` and `r`."

**Formalization Note.**
* The family: for each `n`, a QAC circuit `C n` of depth `d n` on `q n` qubits (`Fin (q n)`, no
  geometry) with controls `ctrl n` and accumulator `acc n`, an exact clean implementation of
  `U_⊕n` (published `GeoQAC.IsCleanParity`) with `q n ≤ A n^c` and `gateCount (C n) ≤ A n^c`.
  These are assumed for `n ≥ 2` only (the conclusion only uses block sizes `⌈n^{1/r}⌉ ≥ 2`).
* `1 ≤ r ≤ ⌊log₂ n⌋` is `1 ≤ r ∧ 2^r ≤ n`. `B` and the exponent `e` may depend on `c`, `A` and the
  family but not on `n` or `r`. The depth bound evaluates the family's depth function at
  `⌈n^{1/r}⌉` (`Nat.ceil` of the real `n^{1/r}`). "Polynomial-size" is `gateCount ≤ B n^e`.
* The new circuit is a `[w, h]`-2D-QAC circuit with its logical qubits anywhere; ancillas `|0⟩`. -/
theorem theorem_3_20 (c A : ℝ) (hc : 1 ≤ c) (d q : ℕ → ℕ)
    (C : (n : ℕ) → QACCircuit (Fin (q n)) (d n)) (ctrl : (n : ℕ) → Fin n ↪ Fin (q n))
    (acc : (n : ℕ) → Fin (q n))
    (hclean : ∀ n : ℕ, 2 ≤ n → IsCleanParity (C n) (ctrl n) (acc n))
    (hq : ∀ n : ℕ, 2 ≤ n → (q n : ℝ) ≤ A * (n : ℝ) ^ c)
    (hg : ∀ n : ℕ, 2 ≤ n → (gateCount (C n) : ℝ) ≤ A * (n : ℝ) ^ c) :
    ∃ B e : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n → ∀ r : ℕ, 1 ≤ r → 2 ^ r ≤ n →
      ∃ (w h D : ℕ) (C' : QACCircuit (Pos w h) D) (ctrl' : Fin n ↪ Pos w h) (acc' : Pos w h),
        C'.Is2D ∧ IsCleanParity C' ctrl' acc' ∧
        (w : ℝ) ≤ B * r * (n : ℝ) ^ (c / r) ∧
        (h : ℝ) ≤ B * 2 ^ r * (n : ℝ) ^ (1 + (c - 1) / r) ∧
        (D : ℝ) ≤ B * r * d (Nat.ceil ((n : ℝ) ^ ((1 : ℝ) / r))) ∧
        (gateCount C' : ℝ) ≤ B * (n : ℝ) ^ e := by sorry

end GeoQAC.Supplement
