-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_lemma_2_5
-- name    : LpSubspaceCoreset.SmallP.lemma_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:49:10.170832+00:00
-- url     : https://prove2.me/theorems/1fc8e04b-c76f-445f-a2cb-dfe8fd778669
-- title:
--   Lemma 2.5 — Woodruff–Yasuda bicriteria subspace
-- statement:
--   Fix $1\le p<2$. There are $C_p\ge1$, $c\ge0$ and $\Gamma_0\ge1$ depending only on $p$ such that for every $\delta'>0$ there are one admissible program $P$ of the randomized real RAM and $K>0$ with the following property. For every $N\ge1$, $1\le k<d$, $A\in\mathbb R^{N\times d}$ given by a sparse listing, and $\delta\in(0,1/2)$:
--   - on every coin tape $P$ halts within $K(\log(N+d+1/\delta+2))^c\big(\mathrm{nnz}(A)+|J|^{\omega+\delta'}\big)$ steps and returns a set $J$ of row indices with $|J|\le C_pk(\log(C_pN/\delta))^{C_p}$;
--   - with probability at least $1-\delta$, $F_0=\operatorname{span}\{a_i:i\in J\}$ satisfies $\mathrm{cost}_A(F_0)\le\Gamma_0\,\mathrm{OPT}_A$.
--
--   It provides the low-rank split of Proposition 4.1.
--
--   Differences from the source:
--   - reading: a randomized algorithm (no machine named) → one admissible program of the mission's unit-cost randomized real RAM (SmaleNinth core + integer pointers/memory, guarded rpow, fair-coin tape, halt; rational literals), chosen after δ′ together with K and before the instance; reason: the paper names no machine; this is the standard unit-cost real RAM with the real powers Lewis weights need and fair coins for randomness
--   - reading: Õ_p(·) running time → K·(log(N + d + 1/δ + 2))^c·(·), with c (and C_p) fixed before δ′ and K after δ′; reason: Õ suppresses logarithmic factors in the relevant parameters with p-dependent constants (§2.1, p. 8)
--   - reading: |J|^ω → |J|^(ω+δ′) for every δ′ > 0, ω = OAI.MatrixMultiplication.Arithmetic.omega ℂ; reason: ω is an infimum of admissible exponents and need not be attained
--   - reading: support size and running time (stated unconditionally) → hold on every coin tape; reason: the statement bounds them without a probability; the worst-case reading over all coin tapes
--   - encoding: A ∈ ℝ^{n×d} as input, the returned weighted row subset → integer input (n, d, k, nnz(A), positions of a sparse listing in any order), real input (parameters, entry values); output s, indices, positive weights in negative memory cells, decoded to S ∈ ℝ^{s×n} with rows s_j e_{i_j}^⊤; reason: an input/output layout for the machine; repeated indices merge exactly as in Definition 2.1
--   - encoding: with probability at least … → coinTape measure (infinite product of fair coins) of the set of tapes whose halted output satisfies the guarantee; reason: the algorithm's randomness is its coin tape
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 10, Lemma 2.5

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_LpSubspaceCoreset_SmallP_Cost
import Definitions.Def_LpSubspaceCoreset_SmallP_Machine
import Definitions.Def_LpSubspaceCoreset_SmallP_Instance

namespace LpSubspaceCoreset.SmallP

/-- **Lemma 2.5** (Woodruff–Yasuda bicriteria subspace), p. 10.

For every `p ∈ [1, 2)` there are `C_p ≥ 1`, `c ≥ 0` and `Γ₀ ≥ 1` (depending only on `p`) such that
for every `δ' > 0` there are one admissible program `P` and `K > 0` such that for every `N ≥ 1`,
`1 ≤ k < d`, `A ∈ ℝ^{N×d}` given by a sparse listing, and `δ ∈ (0, 1/2)` (real input `[p, δ]`):
* on every coin tape the run halts within `K (log(N + d + 1/δ + 2))^c (nnz(A) + |J|^{ω+δ'})` steps
  with a set `J` of row indices in `[N]` of size `|J| ≤ C_p k (log(C_p N/δ))^{C_p}`;
* with probability at least `1 − δ`, `F₀ = span{a_i : i ∈ J}` has `cost_A(F₀) ≤ Γ₀ OPT_A`. -/
theorem lemma_2_5 :
    ∀ p : ℝ, 1 ≤ p → p < 2 →
    ∃ Cp c Γ₀ : ℝ, 1 ≤ Cp ∧ 0 ≤ c ∧ 1 ≤ Γ₀ ∧
    ∀ δ' : ℝ, 0 < δ' →
    ∃ (P : Program) (_ : Admissible P) (K : ℝ), 0 < K ∧
    ∀ (N d k : ℕ), 1 ≤ N → 1 ≤ k → k < d →
    ∀ (A : Matrix (Fin N) (Fin d) ℝ) (L : List (Fin N × Fin d)), IsSparseListing A L →
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      (∀ ω : ℕ → Bool, ∃ t : ℕ,
        (t : ℝ) ≤ K * (Real.log ((N : ℝ) + d + 1 / δ + 2)) ^ c *
          ((nnz A : ℝ) + ((outRows N (run P (inputState k [p, δ] A L) ω t)).card : ℝ) ^
            (OAI.MatrixMultiplication.Arithmetic.omega ℂ + δ')) ∧
        (run P (inputState k [p, δ] A L) ω t).halted = true ∧
        ValidIndexOutput N (run P (inputState k [p, δ] A L) ω t) ∧
        ((outRows N (run P (inputState k [p, δ] A L) ω t)).card : ℝ) ≤
          Cp * k * (Real.log (Cp * N / δ)) ^ Cp) ∧
      ENNReal.ofReal (1 - δ) ≤ coinTape {ω | ∃ t : ℕ,
        (run P (inputState k [p, δ] A L) ω t).halted = true ∧
        cost p A (Submodule.span ℝ
          (rowVec A '' ↑(outRows N (run P (inputState k [p, δ] A L) ω t)))) ≤
          Γ₀ * OPT p k A} := by sorry

end LpSubspaceCoreset.SmallP
