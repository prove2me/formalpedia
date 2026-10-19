-- Prove2me | Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_native_chart_partition_s2
-- name    : OAI.Erdos3.RationalFilteredNilmanifold.exists_native_chart_partition_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:35:34.523037+00:00
-- url     : https://prove2.me/theorems/7c3038d2-3fc0-4401-aeb8-02adf55ac430
-- title:
--   A rational filtered nilmanifold of complexity p has a Lipschitz partition of unity subordinate to exp((p+2)^C) small coordinate charts
-- statement:
--   Let $s$ be a natural number. Then there is a natural number $C \ge 2$ with the following property. Let $L$ be a Lie algebra over $\mathbb{Q}$, let $d$ be a natural number, and fix a topology on $\mathbb{R} \otimes_{\mathbb{Q}} L$ making it a Hausdorff topological additive group on which scalar multiplication by $\mathbb{R}$ is continuous. Let $D$ be a `RationalFilteredNilmanifold L s d` (a structure defined by OpenAI: a nilpotent Lie filtration of $L$ of degree $s$, a $\mathbb{Q}$-basis `D.basis` of $L$ indexed by $\operatorname{Fin} d$, bases of the filtration layers, and a lattice subgroup of the associated Baker–Campbell–Hausdorff group whose basis coordinates are squeezed between two grids of mesh determined by a positive integer `D.grid`). Write `D.RealGroup` for the real Baker–Campbell–Hausdorff group of $\mathbb{R} \otimes_{\mathbb{Q}} L$ (with elements $g$ having Lie algebra coordinate $g.\mathrm{coord} \in \mathbb{R} \otimes_{\mathbb{Q}} L$), `D.Space` for its quotient by the image of the lattice, equipped with OpenAI's metric `D.metricSpace`, and $e_{\mathbb{R}}$ = `D.basis.baseChange ℝ` for the real basis of $\mathbb{R} \otimes_{\mathbb{Q}} L$. Let $p \ge 0$ be a real number with `D.GeometryComplexityLE p`, i.e. (as defined by OpenAI) $d \le p$, $\texttt{D.grid} \le e^p$, and all structure constants of `D.basis` and all `D.basis`-coordinates of the layer basis vectors have rational log-height at most $p$. Write $M = e^{(p+2)^C}$.
--
--   Then there are:
--   - a real number $r$ with $0 < r \le 1$ and $1/r \le M$;
--   - a natural number $n$ with $0 < n \le M$;
--   - points $\mathrm{centers}_j \in$ `D.RealGroup` for $j \in \operatorname{Fin} n$, all of whose coordinates $e_{\mathbb{R}}.\mathrm{repr}(\mathrm{centers}_j.\mathrm{coord})_i$ have absolute value at most $M$;
--   - open partial homeomorphisms $\phi_j$ from $\mathbb{R}^{d}$ (functions $\operatorname{Fin} d \to \mathbb{R}$) to `D.Space`, for $j \in \operatorname{Fin} n$, such that $\phi_j(v)$ is the class of $\mathrm{centers}_j \cdot g_v$ for every $v$ (as a function on all of $\mathbb{R}^d$), where $g_v \in$ `D.RealGroup` is the element whose coordinate vector in the basis $e_{\mathbb{R}}$ is $v$ (the inverse of `NilpotentLieBCHGroup.basisHomeomorph` $e_{\mathbb{R}}$), and the source of $\phi_j$ is exactly $\{v : |v_i| < r \text{ for all } i\}$;
--   - a real number $P \ge 0$ with $P \le M$, and functions $f_j :$ `D.Space` $\to \mathbb{R}$ for $j \in \operatorname{Fin} n$, such that $0 \le f_j(x) \le 1$ for all $j, x$; $\sum_j f_j(x) = 1$ for all $x$; each $f_j$ has compact support and its topological support is contained in the target of $\phi_j$; each $f_j$ is $P$-Lipschitz; and the topological support of each $f_j$ is contained in $\phi_j$ of the closed ball of radius $3r/4$ about $0$ in $\mathbb{R}^d$ (sup metric);
--   - a real number $K \ge 0$ with $K \le M$ such that each $\phi_j$ is $K$-Lipschitz on its source (with $\mathbb{R}^d$ carrying the sup metric and `D.Space` the metric `D.metricSpace`).
--
--   Lean: `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_chart_partition_s2`, which states OpenAI's `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_chart_partition` (in `lean/OAI/Combinatorics/Progressions/Geometry/NativeChartPartition.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B101` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/NativeChartPartition.lean (declaration OAI.Erdos3.RationalFilteredNilmanifold.exists_native_chart_partition)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B101

section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

theorem exists_native_chart_partition_s2 (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      letI := D.metricSpace
      ∃ r : ℝ≥0, 0 < r ∧ r ≤ 1 ∧ 1 / (r : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        ∃ centers : Fin n → D.RealGroup,
        ∃ phi : Fin n → OpenPartialHomeomorph (Fin d → ℝ) D.Space,
          (∀ j i, |(D.basis.baseChange ℝ).repr (centers j).coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
          (∀ j v, phi j v = QuotientGroup.mk
            (centers j * (NilpotentLieBCHGroup.basisHomeomorph (D.basis.baseChange ℝ)).symm v)) ∧
          (∀ j, (phi j).source = {v | ∀ i, |v i| < (r : ℝ)}) ∧
          ∃ P : ℝ≥0, (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
          ∃ f : Fin n → D.Space → ℝ,
            (∀ j x, 0 ≤ f j x ∧ f j x ≤ 1) ∧ (∀ x, ∑ j, f j x = 1) ∧
            (∀ j, HasCompactSupport (f j) ∧ tsupport (f j) ⊆ (phi j).target) ∧
            (∀ j, LipschitzWith P (f j)) ∧
            (∀ j, tsupport (f j) ⊆ phi j '' Metric.closedBall 0 (3 * (r : ℝ) / 4)) ∧
            ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
              ∀ j, LipschitzOnWith K (phi j) (phi j).source := by
  sorry

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end
