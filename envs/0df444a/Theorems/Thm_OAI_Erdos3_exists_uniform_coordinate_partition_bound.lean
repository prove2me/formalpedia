-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_uniform_coordinate_partition_bound
-- name    : OAI.Erdos3.exists_uniform_coordinate_partition_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T23:21:19.295002+00:00
-- url     : https://prove2.me/theorems/340e9f10-ecc6-4e0f-b14f-5e621cb3e638
-- title:
--   One pair of constants serves the polynomial coordinate partition bound up to degree s
-- statement:
--   For every natural number $s$ there exist a real number $K$ and a natural number $p$ with $1 \le K$ and $0 < p$ such that for every natural number $h \le s$, `PolynomialCoordinatePartitionBound h K p` holds (at a fixed universe level $u$). Here `PolynomialCoordinatePartitionBound k K p` is OpenAI's predicate: for every finite type $\iota$ (in universe $u$) and polynomials $P_j \in \mathbb{R}[x]$ ($j \in \iota$) of degree at most $k$, and all natural numbers $N, H$ with $0 < H$, $K(|\iota| + 1) \le H$ and $H^{p(|\iota|+1)^{2k}} \le N$, there exist a `FiniteProgressionPartition N` $Q$ (a finite family of arithmetic progressions $\mathrm{start}_i + \mathrm{step}_i \cdot n$, $n < \mathrm{length}_i$, with positive steps, partitioning $\{0, \dots, N-1\}$) together with $z : Q.\mathrm{Label} \to \mathbb{R}^\iota$ and $m : Q.\mathrm{Label} \to \mathbb{N} \to \mathbb{Z}^\iota$, such that $|Q.\mathrm{Label}| \cdot H \le 2^k N$ and, for every label $i$, every $n < \mathrm{length}_i$ and every $j$, $\bigl|P_j(\mathrm{start}_i + \mathrm{step}_i\, n) - m_{i,n,j} - z_{i,j}\bigr| \le k/H$.
--
--   Lean: `OAI.Erdos3.exists_uniform_coordinate_partition_bound` in `lean/OAI/Combinatorics/Progressions/Geometry/UniformCoordinatePartition.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B100` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/UniformCoordinatePartition.lean#L19

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B100

namespace OAI

section

namespace Erdos3

universe u

theorem exists_uniform_coordinate_partition_bound (s : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧
      ∀ h ≤ s, PolynomialCoordinatePartitionBound.{u} h K p := by
  sorry

end Erdos3
end
end OAI
