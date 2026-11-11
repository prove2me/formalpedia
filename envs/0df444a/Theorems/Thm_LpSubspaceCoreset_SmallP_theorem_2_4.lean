-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_theorem_2_4
-- name    : LpSubspaceCoreset.SmallP.theorem_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:49:00.0938+00:00
-- url     : https://prove2.me/theorems/565debe9-e77a-4779-9256-8feb92b1fc61
-- title:
--   Theorem 2.4 — Woodruff–Yasuda pre-sparsification
-- statement:
--   Fix $p\in[1,\infty)\setminus\{2\}$. There are $C_p\ge1$ and $c\ge0$ such that for every $\delta'>0$ there are one admissible program $P$ and $K>0$ with the following property. For every $N\ge1$, $1\le k<d$, $A\in\mathbb R^{N\times d}$ given by a sparse listing, and $\xi,\delta\in(0,1/2)$:
--   - on every coin tape $P$ halts within $K(\log(N+d+1/\xi+1/\delta+2))^c\big(\mathrm{nnz}(A)+d^{\omega+\delta'}\big)$ steps and returns a weighted row subset $A_0=S_0A$ whose support size is at most
--   $$\begin{cases}C_pk\,\xi^{-4/p}\big(\log\frac{C_pk}{\xi\delta}\big)^{C_p},&1\le p<2,\\ C_pk^{p/2}\xi^{-p}\big(\log\frac{C_pk}{\xi\delta}\big)^{C_p},&p>2;\end{cases}\qquad(2.1)$$
--   - with probability at least $1-\delta$, $\mathrm{cost}_{A_0}(F)=(1\pm\xi)\mathrm{cost}_A(F)$ for every $F\in\mathcal F_k$.
--
--   The main theorem uses it to make all logarithmic factors independent of the number of rows.
--
--   Differences from the source:
--   - reading: a randomized algorithm (no machine named) → one admissible program of the mission's unit-cost randomized real RAM (SmaleNinth core + integer pointers/memory, guarded rpow, fair-coin tape, halt; rational literals), chosen after δ′ together with K and before the instance; reason: the paper names no machine; this is the standard unit-cost real RAM with the real powers Lewis weights need and fair coins for randomness
--   - reading: Õ_p(·) running time → K·(log(N + d + 1/ξ + 1/δ + 2))^c·(·), with c (and C_p) fixed before δ′ and K after δ′; reason: Õ suppresses logarithmic factors in the relevant parameters with p-dependent constants (§2.1, p. 8)
--   - reading: d^ω → d^(ω+δ′) for every δ′ > 0, ω = OAI.MatrixMultiplication.Arithmetic.omega ℂ; reason: ω is an infimum of admissible exponents and need not be attained
--   - reading: support size and running time (stated unconditionally) → hold on every coin tape; reason: the statement bounds them without a probability; the worst-case reading over all coin tapes
--   - encoding: A ∈ ℝ^{n×d} as input, the returned weighted row subset → integer input (n, d, k, nnz(A), positions of a sparse listing in any order), real input (parameters, entry values); output s, indices, positive weights in negative memory cells, decoded to S ∈ ℝ^{s×n} with rows s_j e_{i_j}^⊤; reason: an input/output layout for the machine; repeated indices merge exactly as in Definition 2.1
--   - encoding: with probability at least … → coinTape measure (infinite product of fair coins) of the set of tapes whose halted output satisfies the guarantee; reason: the algorithm's randomness is its coin tape
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 9, Theorem 2.4

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_LpSubspaceCoreset_SmallP_Cost
import Definitions.Def_LpSubspaceCoreset_SmallP_Machine
import Definitions.Def_LpSubspaceCoreset_SmallP_Instance

namespace LpSubspaceCoreset.SmallP

/-- **Theorem 2.4** (Woodruff–Yasuda pre-sparsification [WY25]), p. 9.

For every `p ∈ [1, ∞) \ {2}` there are `C_p ≥ 1` and `c ≥ 0` such that for every `δ' > 0` there
are one admissible program `P` and `K > 0` such that for every `N ≥ 1`, `1 ≤ k < d`,
`A ∈ ℝ^{N×d}` given by a sparse listing, and `ξ, δ ∈ (0, 1/2)` (real input `[p, ξ, δ]`):
* on every coin tape the run halts within `K (log(N + d + 1/ξ + 1/δ + 2))^c (nnz(A) + d^{ω+δ'})`
  steps with a weighted row subset (indices in `[N]`, positive weights) whose support size is at
  most `C_p k ξ^{−4/p} (log(C_p k/(ξδ)))^{C_p}` for `1 ≤ p < 2` and
  `C_p k^{p/2} ξ^{−p} (log(C_p k/(ξδ)))^{C_p}` for `p > 2` (2.1);
* with probability at least `1 − δ`, the output is a `(1 ± ξ)` strong row coreset of `A`. -/
theorem theorem_2_4 :
    ∀ p : ℝ, 1 ≤ p → p ≠ 2 →
    ∃ Cp c : ℝ, 1 ≤ Cp ∧ 0 ≤ c ∧
    ∀ δ' : ℝ, 0 < δ' →
    ∃ (P : Program) (_ : Admissible P) (K : ℝ), 0 < K ∧
    ∀ (N d k : ℕ), 1 ≤ N → 1 ≤ k → k < d →
    ∀ (A : Matrix (Fin N) (Fin d) ℝ) (L : List (Fin N × Fin d)), IsSparseListing A L →
    ∀ ξ δ : ℝ, 0 < ξ → ξ < 1 / 2 → 0 < δ → δ < 1 / 2 →
      (∀ ω : ℕ → Bool, ∃ t : ℕ,
        (t : ℝ) ≤ K * (Real.log ((N : ℝ) + d + 1 / ξ + 1 / δ + 2)) ^ c *
          ((nnz A : ℝ) + (d : ℝ) ^ (OAI.MatrixMultiplication.Arithmetic.omega ℂ + δ')) ∧
        (run P (inputState k [p, ξ, δ] A L) ω t).halted = true ∧
        ValidRowSubsetOutput N (run P (inputState k [p, ξ, δ] A L) ω t) ∧
        ((outRows N (run P (inputState k [p, ξ, δ] A L) ω t)).card : ℝ) ≤
          (if p < 2 then
            Cp * k * ξ ^ (-4 / p) * (Real.log (Cp * k / (ξ * δ))) ^ Cp
          else
            Cp * (k : ℝ) ^ (p / 2) * ξ ^ (-p) * (Real.log (Cp * k / (ξ * δ))) ^ Cp)) ∧
      ENNReal.ofReal (1 - δ) ≤ coinTape {ω | ∃ t : ℕ,
        (run P (inputState k [p, ξ, δ] A L) ω t).halted = true ∧
        IsStrongCoreset p k ξ A (outMatrix N (run P (inputState k [p, ξ, δ] A L) ω t))} := by sorry

end LpSubspaceCoreset.SmallP
