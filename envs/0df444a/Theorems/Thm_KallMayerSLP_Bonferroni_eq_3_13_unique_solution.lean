-- Prove2me | Theorems.Thm_KallMayerSLP_Bonferroni_eq_3_13_unique_solution
-- name    : KallMayerSLP.Bonferroni.eq_3_13_unique_solution
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:11.143382+00:00
-- url     : https://prove2.me/theorems/5d5bba64-589e-436f-b2ca-1910bbce7460
-- title:
--   The system (3.13) has the unique solution $v_i^*=\mathbb P(\nu=i)$
-- statement:
--   For events $B_1,\dots,B_r$, $r\ge1$, on a probability space, a vector $(v_0,\dots,v_r)$ solves the equations
--   $$
--   \sum_{i=0}^{r}\binom{i}{k}v_i=S_k,\qquad k=0,\dots,r,
--   $$
--   of the system (3.13) if and only if $v_i=\mathbb P(\nu=i)$ for all $i$. The solution is nonnegative, and
--   $$
--   \mathbb P(\nu\ge1)=\sum_{i=1}^{r}\mathbb P(\nu=i).
--   $$
--   The coefficient matrix is upper triangular with nonzero diagonal, which is why the solution is unique.
--
--   Differences from the source:
--   - encoding: events $B_1,\dots,B_r$ (or variables $v_1,\dots,v_r$) indexed by $1,\dots,r$ → indexed by `Fin r`, that is by $0,\dots,r-1$; reason: Lean convention; same instances
--   - encoding: the number $r$ of events $B_1,\dots,B_r$ (the dimension of $\xi$ with values in $\mathbb R^r$) is left implicit → hypothesis `1 ≤ r`; reason: the family $B_1,\dots,B_r$ starts at $B_1$, so the book has $r\ge1$; the hypothesis excludes only the empty family
--   - encoding: the equations of (3.13) each start at the diagonal term $v_k$ → each equation sums over $i=0,\dots,r$; reason: $\binom{i}{k}=0$ for $i<k$, so the terms added vanish
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.13), p.287 (PDF 296)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_occurrenceCount

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- The equation part of the system (3.13) has the unique solution `v_i* = ℙ(ν = i)`,
`i = 0, …, r`, which is nonnegative, and `ℙ(ν ≥ 1) = ∑_{i=1}^r ℙ(ν = i)`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.13), p.287 (PDF 296).

**Formalization Note.** The variables `v₀, …, v_r` are `v : Fin (r + 1) → ℝ`, and the `k`-th
equation of (3.13), `k = 0, …, r`, is `∑_{i ≥ k} (i choose k) v_i = S_k`, where `S₀ = 1`. -/
theorem eq_3_13_unique_solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) :
    (∀ v : Fin (r + 1) → ℝ,
      (∀ k : Fin (r + 1), ∑ i : Fin (r + 1), (((i : ℕ).choose (k : ℕ) : ℕ) : ℝ) * v i =
        binomialMoment μ B k) ↔
      ∀ i : Fin (r + 1), v i = μ.real {ω | occurrenceCount B ω = i}) ∧
    (∀ i : ℕ, 0 ≤ μ.real {ω | occurrenceCount B ω = i}) ∧
    μ.real {ω | 1 ≤ occurrenceCount B ω} =
      ∑ i ∈ Finset.Icc 1 r, μ.real {ω | occurrenceCount B ω = i} := by sorry

end KallMayerSLP.Bonferroni
