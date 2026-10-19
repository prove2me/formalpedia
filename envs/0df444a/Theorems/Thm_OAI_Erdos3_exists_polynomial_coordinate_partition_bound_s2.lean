-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_polynomial_coordinate_partition_bound_s2
-- name    : OAI.Erdos3.exists_polynomial_coordinate_partition_bound_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:31:18.411637+00:00
-- url     : https://prove2.me/theorems/8bb1b2f5-0d9c-416d-ac10-bbb924738efa
-- title:
--   For each degree k, finitely many real polynomials can be simultaneously approximated modulo 1 on the progressions of a partition of [0, N)
-- statement:
--   For every natural number $k$ there exist a real number $K \ge 1$ and a natural number $p > 0$ such that `PolynomialCoordinatePartitionBound k K p` holds (for the fixed universe level $u$ of the statement). Here `PolynomialCoordinatePartitionBound k K p` is a proposition defined by OpenAI, saying the following.
--
--   For every finite type $\iota$ (in universe $u$) with $|\iota|$ elements, every family $(P_j)_{j \in \iota}$ of real polynomials with $\deg P_j \le k$ for all $j$, and all natural numbers $N, H$ with $H > 0$, $K(|\iota| + 1) \le H$ and $H^{p\,(|\iota|+1)^{2k}} \le N$, there exist
--   - a partition $Q$ of $\{0, 1, \dots, N-1\}$ into arithmetic progressions, given (as an OpenAI `FiniteProgressionPartition N`) by a finite label set and, for each label $i$, a start $a_i \in \mathbb{N}$, a step $d_i \in \mathbb{N}$ with $d_i > 0$ and a length $\ell_i \in \mathbb{N}$, together with a bijection from the pairs $(i, n)$ with $n < \ell_i$ onto $\{0, \dots, N-1\}$ sending $(i, n)$ to $a_i + d_i n$;
--   - real numbers $z_{i,j}$ (for each label $i$ and each $j \in \iota$);
--   - integers $m_{i,n,j}$ (for each label $i$, each $n \in \mathbb{N}$ and each $j \in \iota$),
--
--   such that (number of labels of $Q$)$\cdot H \le 2^{k} N$, and for every label $i$, every $n < \ell_i$ and every $j \in \iota$,
--   $$\bigl|P_j(a_i + d_i n) - m_{i,n,j} - z_{i,j}\bigr| \le \frac{k}{H}.$$
--
--   Lean: `OAI.Erdos3.exists_polynomial_coordinate_partition_bound_s2`, which states OpenAI's `OAI.Erdos3.exists_polynomial_coordinate_partition_bound` (in `lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialCoordinatePartition.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B093` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialCoordinatePartition.lean (declaration OAI.Erdos3.exists_polynomial_coordinate_partition_bound)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B093

section

namespace OAI

section

namespace Erdos3

universe u

open Polynomial

theorem exists_polynomial_coordinate_partition_bound_s2 (k : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧ PolynomialCoordinatePartitionBound.{u} k K p := by
  sorry

end Erdos3

end

end OAI
end
