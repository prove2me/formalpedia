-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_Supplement_lemma_4_10
-- name    : LatticeAvgPrec.OneVector.Supplement.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:41:30.974021+00:00
-- url     : https://prove2.me/theorems/4340a719-afe3-43a4-996a-4a936bfb2c1f
-- title:
--   Lemma 4.10 — Inverse columns modulo one
-- statement:
--   Fix $2<\omega\le3$ available. There are a program $\mathcal P$ and a subpolynomial factor $g$ such that the following holds. Let $\mathcal L\in\mathbb Z^{N\times N}$, $N\ge1$, be nonsingular, with total column bitlength
--
--   $$
--   B_0=\sum_{j}\max_i\mathrm{bits}(\mathcal L_{ij})
--   $$
--
--   (a column's bitlength is its largest signed entry bitlength). Let $p\in\mathbb N^N$: column $j$ is *selected* when $p_j\ge1$, and then $p_j$ is its prescribed precision. On input $(\mathcal L,p)$, $\mathcal P$ is Las Vegas and outputs dyadic numbers $x_{ij}=\mathrm{num}_{ij}/2^{e_j}$ such that, for every selected column $j$ and every $i$,
--
--   $$
--   x_{ij}-(\mathcal L^{-1})_{ij}\in\mathbb Z+[-2^{-p_j},2^{-p_j}],
--   $$
--
--   in expected
--
--   $$
--   g\Bigl(N,\ B_0+\sum_jp_j\Bigr)\,N^{\omega-1}\Bigl(B_0+N+\sum_j p_j\Bigr)
--   $$
--
--   bit operations, input and output included.
--
--   This computes columns of $\mathcal L^{-1}\bmod 1$ at individual precisions with a cost driven by the total column bitlength; in the paper it recovers the corrected lift of the child basis (Lemma 4.11).
--
--   **Formalization Note** The selection and the precisions form one vector $p$, so $\sum_j p_j$ runs over the selected columns. The output is a numerator matrix with one binary exponent per column; unselected columns are unconstrained. $B_0$ is the published total row bitlength of $\mathcal L^{\mathsf T}$. $\widetilde O$ follows the conventions of §1.1.1 (p.4), as in the published goal: $\widetilde O$ suppresses a subpolynomial factor in the dimension and precision parameters, chosen with the program after $\omega$ and before every input.
--
--   Differences from the source:
--   - encoding: selected columns j with prescribed integers p_j ≥ 1 → a vector p ∈ ℕ^N, column j selected iff p_j ≥ 1; reason: the selected set and Σ_j p_j over it are unchanged
--   - encoding: computed entries of the selected columns → a numerator matrix and one exponent per column, all N columns written, only selected columns constrained; reason: a dyadic output format; writing zeros in unselected columns costs O(N²), within the bound
--   - reading: expected Õ(N^{ω−1}(B_0 + N + Σ_j p_j)) time → LasVegasWithin with bound g(N, B_0 + Σp) N^{ω−1}(B_0 + N + Σp), g subpolynomial; reason: the Õ convention of §1.1.1; time = bit operations of the published RAM
--   - encoding: order N → 1 ≤ N; reason: excludes the empty matrix, where the bound is 0
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Lemma 4.10, p.19 (proof App. B.3, pp.31–32)

import Definitions.Def_LatticeAvgPrec_OneVector_Supplement_Objects
open Matrix

namespace LatticeAvgPrec.OneVector.Supplement

/-- **Lemma 4.10** (Inverse columns modulo one; STOC 2027 submission #1574, p.19). Let `𝓛` be a
nonsingular integer matrix of order `N` and total column bitlength `B_0`. For prescribed integers
`p_j ≥ 1`, selected columns of `𝓛⁻¹ mod 1` can be computed in expected
`Õ(N^{ω−1}(B_0 + N + Σ_j p_j))` time. In column `j`, each computed entry differs from the true entry
by an integer plus an error of absolute value at most `2^{−p_j}`.

**Formalization Note** The selection and the precisions are one vector `p ∈ ℕ^N`: column `j` is
selected exactly when `p_j ≥ 1`, and then `p_j` is its prescribed precision, so `Σ_j p_j` is the sum
over the selected columns. `B_0 = Σ_j max_i bits(𝓛_ij)` is the total row bitlength of `𝓛ᵀ`. The
output is a numerator matrix with one binary exponent per column; only selected columns are
constrained. -/
theorem lemma_4_10 (ω : ℝ) (hω₁ : 2 < ω) (hω₂ : ω ≤ 3) (hM : MatMulAvailable ω) :
    ∃ (P : TimeSpaceMA.Program) (g : ℕ → ℕ → ℝ), IsSubpoly g ∧
      ∀ (N : ℕ) (L : Matrix (Fin N) (Fin N) ℤ) (p : Fin N → ℕ), 1 ≤ N → L.det ≠ 0 →
        SoftmaxAttnFD.LasVegasWithin P
          (TimeSpaceMA.memOf (matCode L ++ vecCode (fun j => (p j : ℤ))))
          (fun mem => ∃ (num : Matrix (Fin N) (Fin N) ℤ) (ex : Fin N → ℕ),
            memHolds mem (matCode num ++ vecCode (fun j => (ex j : ℤ))) ∧
            ∀ i j, 1 ≤ p j → ∃ z : ℤ,
              |dyVal (num i j) (ex j) - (rmat L)⁻¹ i j - z| ≤ (2 : ℝ) ^ (-(p j : ℝ)))
          (g N (totalRowBits Lᵀ + ∑ j, p j) * (N : ℝ) ^ (ω - 1) *
            ((totalRowBits Lᵀ : ℝ) + N + ∑ j, (p j : ℝ))) := by sorry

end LatticeAvgPrec.OneVector.Supplement
