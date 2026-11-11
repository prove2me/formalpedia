-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_proposition_4_1
-- name    : LpSubspaceCoreset.SmallP.proposition_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:49:08.154635+00:00
-- url     : https://prove2.me/theorems/13139b0d-5d5c-4d1e-8db2-94ae05e82fe0
-- title:
--   Proposition 4.1 — implementing the low-rank-split sampling procedure
-- statement:
--   Fix $1\le p<2$. There are $C_p\ge1$ and $c\ge0$ such that for every $\delta'>0$ there are one admissible program $P$ and $K>0$ with the following property. For every $N\ge1$, $1\le k<d$, $A\in\mathbb R^{N\times d}$ given by a sparse listing, and $0<\varepsilon<1/2$:
--   - on every coin tape $P$ halts within $K(\log(N+d+1/\varepsilon+2))^c\big(\mathrm{nnz}(A)+k^{\omega+\delta'}+k\varepsilon^{-2}\big)$ steps and returns a reweighted row subset supported on at most
--   $$C_pk\varepsilon^{-2}\Big(\log\frac{C_p(N+k)}{\varepsilon}\Big)^{C_p}\qquad(4.1)$$
--   rows;
--   - with probability at least $5/6$ it is a $(1\pm\varepsilon)$ strong row coreset of $A$.
--
--   Applied to the output of Theorem 2.4, it yields the main theorem.
--
--   Differences from the source:
--   - reading: a randomized algorithm (no machine named) → one admissible program of the mission's unit-cost randomized real RAM (SmaleNinth core + integer pointers/memory, guarded rpow, fair-coin tape, halt; rational literals), chosen after δ′ together with K and before the instance; reason: the paper names no machine; this is the standard unit-cost real RAM with the real powers Lewis weights need and fair coins for randomness
--   - reading: Õ_p(·) running time → K·(log(N + d + 1/ε + 2))^c·(·), with c (and C_p) fixed before δ′ and K after δ′; reason: Õ suppresses logarithmic factors in the relevant parameters with p-dependent constants (§2.1, p. 8)
--   - reading: k^ω → k^(ω+δ′) for every δ′ > 0, ω = OAI.MatrixMultiplication.Arithmetic.omega ℂ; reason: ω is an infimum of admissible exponents and need not be attained
--   - reading: support size and running time (stated unconditionally) → hold on every coin tape; reason: the statement bounds them without a probability; the worst-case reading over all coin tapes
--   - encoding: A ∈ ℝ^{n×d} as input, the returned weighted row subset → integer input (n, d, k, nnz(A), positions of a sparse listing in any order), real input (parameters, entry values); output s, indices, positive weights in negative memory cells, decoded to S ∈ ℝ^{s×n} with rows s_j e_{i_j}^⊤; reason: an input/output layout for the machine; repeated indices merge exactly as in Definition 2.1
--   - encoding: with probability at least … → coinTape measure (infinite product of fair coins) of the set of tapes whose halted output satisfies the guarantee; reason: the algorithm's randomness is its coin tape
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 22, Proposition 4.1

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_LpSubspaceCoreset_SmallP_Cost
import Definitions.Def_LpSubspaceCoreset_SmallP_Machine
import Definitions.Def_LpSubspaceCoreset_SmallP_Instance

namespace LpSubspaceCoreset.SmallP

/-- **Proposition 4.1** (Implementing the low-rank-split sampling procedure), p. 22.

For every `p ∈ [1, 2)` there are `C_p ≥ 1` and `c ≥ 0` such that for every `δ' > 0` there are one
admissible program `P` and `K > 0` such that for every `N ≥ 1`, `1 ≤ k < d`, `A ∈ ℝ^{N×d}` given
by a sparse listing, and `ε ∈ (0, 1/2)` (real input `[p, ε]`):
* on every coin tape the run halts within `K (log(N + d + 1/ε + 2))^c (nnz(A) + k^{ω+δ'} + kε^{−2})`
  steps with a reweighted row subset (indices in `[N]`, positive weights) on at most
  `C_p k ε^{−2} (log(C_p (N + k)/ε))^{C_p}` distinct rows (4.1);
* with probability at least `5/6`, the output is a `(1 ± ε)` strong row coreset of `A`. -/
theorem proposition_4_1 :
    ∀ p : ℝ, 1 ≤ p → p < 2 →
    ∃ Cp c : ℝ, 1 ≤ Cp ∧ 0 ≤ c ∧
    ∀ δ' : ℝ, 0 < δ' →
    ∃ (P : Program) (_ : Admissible P) (K : ℝ), 0 < K ∧
    ∀ (N d k : ℕ), 1 ≤ N → 1 ≤ k → k < d →
    ∀ (A : Matrix (Fin N) (Fin d) ℝ) (L : List (Fin N × Fin d)), IsSparseListing A L →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      (∀ ω : ℕ → Bool, ∃ t : ℕ,
        (t : ℝ) ≤ K * (Real.log ((N : ℝ) + d + 1 / ε + 2)) ^ c *
          ((nnz A : ℝ) + (k : ℝ) ^ (OAI.MatrixMultiplication.Arithmetic.omega ℂ + δ') +
            k / ε ^ 2) ∧
        (run P (inputState k [p, ε] A L) ω t).halted = true ∧
        ValidRowSubsetOutput N (run P (inputState k [p, ε] A L) ω t) ∧
        ((outRows N (run P (inputState k [p, ε] A L) ω t)).card : ℝ) ≤
          Cp * k / ε ^ 2 * (Real.log (Cp * (N + k) / ε)) ^ Cp) ∧
      (5 / 6 : ENNReal) ≤ coinTape {ω | ∃ t : ℕ,
        (run P (inputState k [p, ε] A L) ω t).halted = true ∧
        IsStrongCoreset p k ε A (outMatrix N (run P (inputState k [p, ε] A L) ω t))} := by sorry

end LpSubspaceCoreset.SmallP
