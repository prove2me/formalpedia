-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_theorem_1_1
-- name    : LpSubspaceCoreset.SmallP.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:49:02.521178+00:00
-- url     : https://prove2.me/theorems/424d8ead-d2e3-42d6-96d6-5fc5c61fb75b
-- title:
--   Theorem 1.1 — strong row coresets of Õ_p(kε⁻²) rows for 1 ≤ p < 2 in Õ_p(nnz(A) + d^ω + kε⁻²) time
-- statement:
--   Fix $1\le p<2$. There are constants $C_p\ge1$ and $c\ge0$ such that for every $\delta'>0$ there are one admissible program $P$ of the randomized real RAM and a constant $K>0$ with the following property. For every $n\ge1$, $1\le k<d$, $A\in\mathbb R^{n\times d}$ given by a sparse listing of its nonzero entries, and $\varepsilon\in(0,1/2)$:
--   - on every coin tape $P$ halts within
--   $$K\,\big(\log(n+d+1/\varepsilon+2)\big)^{c}\,\big(\mathrm{nnz}(A)+d^{\omega+\delta'}+k\varepsilon^{-2}\big)$$
--   steps and outputs a reweighted row subset $SA$ (row indices in $[n]$, positive weights) supported on at most $C_pk\varepsilon^{-2}\big(\log\frac{C_pk}{\varepsilon}\big)^{C_p}$ distinct rows;
--   - with probability at least $2/3$ over the coin tape,
--   $$(1-\varepsilon)\,\mathrm{cost}_A(F)\le\mathrm{cost}_{SA}(F)\le(1+\varepsilon)\,\mathrm{cost}_A(F)\quad\text{simultaneously for every subspace }F\subseteq\mathbb R^d,\ \dim F\le k.$$
--   The sampled rows and weights are produced before any $F$ is chosen. The size matches the $\tilde\Omega_p(k\varepsilon^{-2})$ sampling lower bound of Li, Wang and Woodruff when $k+1\ge C\log(1/\varepsilon)$.
--
--   Differences from the source:
--   - reading: a randomized algorithm (no machine named) → one admissible program of the mission's unit-cost randomized real RAM (SmaleNinth core + integer pointers/memory, guarded rpow, fair-coin tape, halt; rational literals), chosen after δ′ together with K and before the instance; reason: the paper names no machine; this is the standard unit-cost real RAM with the real powers Lewis weights need and fair coins for randomness
--   - reading: Õ_p(·) running time → K·(log(n + d + 1/ε + 2))^c·(·), with c (and C_p) fixed before δ′ and K after δ′; reason: Õ suppresses logarithmic factors in the relevant parameters with p-dependent constants (§2.1, p. 8)
--   - reading: d^ω → d^(ω+δ′) for every δ′ > 0, ω = OAI.MatrixMultiplication.Arithmetic.omega ℂ; reason: ω is an infimum of admissible exponents and need not be attained
--   - reading: support size and running time (stated unconditionally) → hold on every coin tape; reason: the statement bounds them without a probability; the worst-case reading over all coin tapes
--   - encoding: A ∈ ℝ^{n×d} as input, the returned weighted row subset → integer input (n, d, k, nnz(A), positions of a sparse listing in any order), real input (parameters, entry values); output s, indices, positive weights in negative memory cells, decoded to S ∈ ℝ^{s×n} with rows s_j e_{i_j}^⊤; reason: an input/output layout for the machine; repeated indices merge exactly as in Definition 2.1
--   - encoding: with probability at least … → coinTape measure (infinite product of fair coins) of the set of tapes whose halted output satisfies the guarantee; reason: the algorithm's randomness is its coin tape
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), pp. 3–4, Theorem 1.1 (proof p. 24)

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_LpSubspaceCoreset_SmallP_Cost
import Definitions.Def_LpSubspaceCoreset_SmallP_Machine
import Definitions.Def_LpSubspaceCoreset_SmallP_Instance

namespace LpSubspaceCoreset.SmallP

/-- **Theorem 1.1** (Strong row coresets for `1 ≤ p < 2`), pp. 3–4.

For every `p ∈ [1, 2)` there are constants `C_p ≥ 1` and `c ≥ 0` such that for every `δ' > 0`
there are one admissible program `P` of the randomized real RAM and a constant `K > 0` such that
for every `n ≥ 1`, `1 ≤ k < d`, `A ∈ ℝ^{n×d}` given by any sparse listing `L` of its nonzero
entries, and `ε ∈ (0, 1/2)`, run on the input `(n, d, k, nnz(A), L; p, ε, entries)`:
* on every coin tape the run halts within
  `K·(log(n + d + 1/ε + 2))^c·(nnz(A) + d^{ω+δ'} + k ε^{−2})` steps, with a reweighted row subset
  (indices in `[n]`, positive weights) on at most `C_p k ε^{−2} (log(C_p k/ε))^{C_p}` distinct rows;
* with probability at least `2/3` over the coin tape, the output `S` satisfies
  `(1 − ε) cost_A(F) ≤ cost_{SA}(F) ≤ (1 + ε) cost_A(F)` simultaneously for every `F` with
  `dim F ≤ k`. -/
theorem theorem_1_1 :
    ∀ p : ℝ, 1 ≤ p → p < 2 →
    ∃ Cp c : ℝ, 1 ≤ Cp ∧ 0 ≤ c ∧
    ∀ δ' : ℝ, 0 < δ' →
    ∃ (P : Program) (_ : Admissible P) (K : ℝ), 0 < K ∧
    ∀ (n d k : ℕ), 1 ≤ n → 1 ≤ k → k < d →
    ∀ (A : Matrix (Fin n) (Fin d) ℝ) (L : List (Fin n × Fin d)), IsSparseListing A L →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      (∀ ω : ℕ → Bool, ∃ t : ℕ,
        (t : ℝ) ≤ K * (Real.log ((n : ℝ) + d + 1 / ε + 2)) ^ c *
          ((nnz A : ℝ) + (d : ℝ) ^ (OAI.MatrixMultiplication.Arithmetic.omega ℂ + δ') +
            k / ε ^ 2) ∧
        (run P (inputState k [p, ε] A L) ω t).halted = true ∧
        ValidRowSubsetOutput n (run P (inputState k [p, ε] A L) ω t) ∧
        ((outRows n (run P (inputState k [p, ε] A L) ω t)).card : ℝ) ≤
          Cp * k / ε ^ 2 * (Real.log (Cp * k / ε)) ^ Cp) ∧
      (2 / 3 : ENNReal) ≤ coinTape {ω | ∃ t : ℕ,
        (run P (inputState k [p, ε] A L) ω t).halted = true ∧
        IsStrongCoreset p k ε A (outMatrix n (run P (inputState k [p, ε] A L) ω t))} := by sorry

end LpSubspaceCoreset.SmallP
