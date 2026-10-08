-- Prove2me | Theorems.Thm_OAI_Erdos3_normalizedBoxPartitions_positive
-- name    : OAI.Erdos3.normalizedBoxPartitions_positive
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T10:30:09.924669+00:00
-- url     : https://prove2.me/theorems/bfdc9678-655c-4f42-8d23-f4edb92fa5e7
-- title:
--   Every block of a normalized box partition has positive length
-- statement:
--   Let $I$ be a type, $N\colon I\to\mathbb N$, $H\colon I\to\mathbb R$ and $\rho\in\mathbb R$, and assume `hlarge`: $4\le\rho H_i$ for every $i$, and `hwhole`: $\rho H_i\le 2N_i$ for every $i$. For every $i\in I$ and every label $c$ of the partition `normalizedBoxPartitions N H ρ hlarge hwhole i`, the length of block $c$ is positive. Here `normalizedBoxPartitions N H ρ hlarge hwhole` assigns to each $i$ a `FiniteProgressionPartition (N i)` (a structure bundling a finite label type and, for each label, a start, a positive step and a length, together with a bijection from the disjoint union of the blocks $\{\text{start}+\text{step}\cdot j : j<\text{length}\}$ onto $\{0,\dots,N_i-1\}$); it is `comparableBoxPartitions` with target lengths $\lfloor\rho H_i/2\rfloor$, a partition of $\{0,\dots,N_i-1\}$ into merged intervals of step $1$.
--
--   Lean: `OAI.Erdos3.normalizedBoxPartitions_positive` in `lean/OAI/Combinatorics/Progressions/Sampling/PhysicalGridCorrelation.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B013` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/PhysicalGridCorrelation.lean#L33

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B013

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem normalizedBoxPartitions_positive {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    0 < (normalizedBoxPartitions N H ρ hlarge hwhole i).length c := by
  sorry

end Erdos3
end
end OAI
