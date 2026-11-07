-- Prove2me | Theorems.Thm_LosslessCond_lemma_4_1
-- name    : LosslessCond.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:33:40.398827+00:00
-- url     : https://prove2.me/theorems/1872d347-6553-4032-a3fc-386749785dee
-- title:
--   Lemma 4.1 — rank and input values: $\le 2^r$ values, $r\le 2^{s-1}$, nonsingular minors, large input sets
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a finite Boolean matrix of real rank $r$, and $D(M)$ its deterministic communication complexity.
--
--   1. $M$ has at most $2^r$ distinct row values and at most $2^r$ distinct column values. In particular $D(M)\le r+1$.
--   2. If $D(M)\le s$ and $s\ge 1$, then $r\le 2^{s-1}$.
--   3. For each integer $1\le q\le r$, $M$ contains a nonsingular $q\times q$ submatrix on original indices. Moreover, for $k\ge 1$, every nonsingular $2^k\times 2^k$ Boolean matrix $N$ has $D(N)=k+1$ exactly.
--   4. If $D(M)\ge d\ge 2$, then $|X|>2^{d-2}$ and $|Y|>2^{d-2}$.
--
--   A row value is the whole Boolean vector $(M(x,y))_{y\in Y}$, as opposed to the label $x$. Parts 3 and 4 supply the hard minors and the spare labels used by Theorems 5.4 and 5.5.
--
--   Differences from the source:
--   - encoding: a nonsingular q-by-q submatrix on original indices → injective index maps Fin q → X, Fin q → Y whose real 0/1 matrix has nonzero determinant; reason: same objects; injectivity makes the indices distinct original labels
--   - encoding: a nonsingular 2^k-by-2^k Boolean matrix → N : Fin (2^k) → Fin (2^k) → Bool with nonzero real determinant; reason: every 2^k-square matrix is such an N after numbering its rows and columns, which changes neither D nor nonsingularity
--   - encoding: number of distinct row (column) values → Set.ncard of the range of x ↦ M x (of y ↦ (x ↦ M x y)); reason: the range is finite, so ncard is its true size
--   - generalization: finite nonempty input sets X, Y → finite types X Y : Type (Fintype), nonemptiness not assumed; reason: every finite nonempty set is equivalent to a type in universe 0, so every instance of the source is covered; the instances with an empty X or Y are additional, and there the statement holds trivially
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Lemma 4.1, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_realRank

namespace LosslessCond

/-- **Lemma 4.1** (Mackenzie, *Lossless Hardness Condensation in Deterministic Communication
Complexity*, arXiv:2609.28691, held version sha256 ce75e6d4…, p.10). Let `M` be a finite total
Boolean matrix of rank `r`.

1. There are at most `2^r` distinct row values and at most `2^r` distinct column values. In
   particular, `D(M) ≤ r + 1`.
2. If `D(M) ≤ s` and `s ≥ 1`, then `r ≤ 2^(s−1)`.
3. For each integer `1 ≤ q ≤ r`, `M` contains a nonsingular `q`-by-`q` submatrix on original
   indices. A nonsingular `2^k`-by-`2^k` Boolean matrix has depth exactly `k + 1` for `k ≥ 1`.
4. If `D(M) ≥ d ≥ 2`, each original input set has more than `2^(d−2)` elements.

**Formalization Note** `r = DetCCHard.realRank M`, the rank over `ℝ` of the `0/1` matrix. A row
value is the function `M x : Y → Bool` and a column value is `fun x => M x y`; their numbers are
`Set.ncard` of the (finite) ranges. A `q`-by-`q` submatrix on original indices is given by
injective index maps `f : Fin q → X`, `g : Fin q → Y`, and nonsingular means nonzero determinant of
the real `0/1` matrix. The second clause of part 3 is stated for every Boolean matrix
`N : Fin (2^k) → Fin (2^k) → Bool` with nonzero determinant. Natural subtraction in `s − 1` and
`d − 2` is exact under `s ≥ 1`, `d ≥ 2`. -/
theorem lemma_4_1 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) :
    ((Set.range M).ncard ≤ 2 ^ DetCCHard.realRank M ∧
      (Set.range fun y x => M x y).ncard ≤ 2 ^ DetCCHard.realRank M ∧
      DetCCHard.Dcost M ≤ DetCCHard.realRank M + 1) ∧
    (∀ s : ℕ, 1 ≤ s → DetCCHard.Dcost M ≤ s → DetCCHard.realRank M ≤ 2 ^ (s - 1)) ∧
    ((∀ q : ℕ, 1 ≤ q → q ≤ DetCCHard.realRank M →
      ∃ (f : Fin q → X) (g : Fin q → Y), Function.Injective f ∧ Function.Injective g ∧
        (Matrix.of fun i j => if M (f i) (g j) then (1 : ℝ) else 0).det ≠ 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ N : Fin (2 ^ k) → Fin (2 ^ k) → Bool,
        (Matrix.of fun i j => if N i j then (1 : ℝ) else 0).det ≠ 0 →
          DetCCHard.Dcost N = k + 1)) ∧
    (∀ d : ℕ, 2 ≤ d → d ≤ DetCCHard.Dcost M →
      2 ^ (d - 2) < Fintype.card X ∧ 2 ^ (d - 2) < Fintype.card Y) := by sorry

end LosslessCond
