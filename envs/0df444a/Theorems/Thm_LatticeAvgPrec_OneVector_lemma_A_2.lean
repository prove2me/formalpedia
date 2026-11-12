-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_lemma_A_2
-- name    : LatticeAvgPrec.OneVector.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:51:24.485182+00:00
-- url     : https://prove2.me/theorems/fad1f153-93ee-4c15-9311-5859827979a6
-- title:
--   Lemma A.2 — Triangular size reduction [KEF21, Alg. 7, Thm. 2]
-- statement:
--   Let $\omega$ be an available exponent, $2<\omega\le3$. There are constants $C,c>0$ such that the following holds. Let $W$ be dyadic upper unitriangular of order $k\ge1$ with $\|W\|_F,\|W^{-1}\|_F\le 2^b$, supplied to working precision $p$, i.e. $W=N/2^p$ with $N$ an integer matrix, where
--   $$p\ge C\bigl(b+k\log_2^2(2k)\bigr).$$
--   Then a deterministic routine of $\widetilde O(k^\omega p)$ bit operations returns an integer upper unitriangular $U$ with
--   $$\|WU\|_F,\ \|(WU)^{-1}\|_F\le 2^{c\log_2^2(2k)},\qquad \|U\|_F\le 2^{b+c\log_2^2(2k)}.$$
--
--   In the proof of Lemma 4.4 this step improves the column-scaled condition number of the reduced basis from $2^{O(k\log k)}$ to $2^{O(k)}$ while keeping the Gram–Schmidt lengths.
--
--   **Formalization Note** The input is $p$ and $N$. $\log^2$ is the square of $\log_2$.
--
--   Differences from the source:
--   - reading: costs measured in bit operations, with quasi-linear scalar integer arithmetic; deterministic cost → bit cost of a program of the published logarithmic-cost RAM (TimeSpaceMA_RAM with the cost layer SoftmaxAttnFD_Machine): each instruction costs 1 plus the bit sizes of every address and value it touches; DeterministicWithin: coin-free, halts within the bound on every tape with a correct output; reason: the paper names no machine; the matrix-multiplication hypothesis MatMulAvailable is stated in the same model, so the reading neither adds nor removes power
--   - reading: Õ(f) suppresses subpolynomial factors in the dimension and precision parameters (p.4) → g(k, p)·f with g subpolynomial (IsSubpoly: for every ε > 0, g x y ≤ C_ε (x + y + 2)^ε), g chosen with the program before every input; reason: the p.4 convention made uniform; a factor fixed before the input is the honest reading of Õ
--   - encoding: binary input and output → integers coded one bit per memory cell (natCode / intCode, self-delimiting), vectors and matrices with their dimensions first, input from cell 0 (memOf), output held from cell 0 (memHolds); reason: keeps the bit count of the binary representation; the codes are prefix-free, so the output is read unambiguously
--   - encoding: a fixed available matrix-multiplication exponent 2 < ω ≤ 3; multiplying order-n integer matrices with b-bit entries costs Õ(n^ω b) (pp.4, 9) → hypotheses 2 < ω ≤ 3 and MatMulAvailable ω (a coin-free RAM program multiplies such matrices within g₀(n,b)·n^ω·b, g₀ subpolynomial); reason: the paper's standing assumption stated as a hypothesis; ω = 3 satisfies it, so the statement is not vacuous
--   - encoding: k×k matrices with an implicit positive dimension → 1 ≤ k; reason: at k = 0 the cost bound is 0 while every run costs at least 1; the 0-dimensional case is degenerate and not considered by the source
--   - reading: p ≥ C(b + w + k log²(2k)), where w is the word size → p ≥ C(b + k log₂²(2k)), no word size; reason: the bit model of §2 has no word; a word of O(log(kp)) bits is absorbed into C(b + k log²(2k)), and the proof of Lemma 4.4 uses p = C(h + k log²(2k)) without w
--   - reading: the input is supplied to that precision → W = N/2^p with N an integer matrix; input (p, N); reason: a dyadic matrix with denominator dividing 2^p, given at precision p
--   - encoding: 2^{O(log²(2k))} → 2^(c·log₂²(2k)) with c > 0 chosen with the program; reason: uniform reading of O(·) in the exponent
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Lemma A.2, p. 27

import Definitions.Def_LatticeAvgPrec_OneVector_Cost
open Matrix

namespace LatticeAvgPrec.OneVector

/-- **Lemma A.2** (Triangular size reduction [KEF21, Algorithm 7 and Theorem 2]; STOC 2027
submission #1574, p.27). Let `W` be dyadic upper unitriangular of order `k` with
`‖W^{±1}‖_F ≤ 2^b`. At working precision `p ≥ C(b + w + k log²(2k))` the routine returns an integer
upper-unitriangular `U` with `‖(WU)^{±1}‖_F ≤ 2^{O(log²(2k))}`, `‖U‖_F ≤ 2^{b + O(log²(2k))}`, in
`Õ(k^ω p)` bit operations; the input is supplied to that precision.

**Formalization Note** The word size `w` is dropped (the bit-cost model has no word; the proof of
Lemma 4.4 uses `p = C(h + k log²(2k))`). The input is `p` and `W = N / 2^p`. -/
theorem lemma_A_2 (ω : ℝ) (hω₁ : 2 < ω) (hω₂ : ω ≤ 3) (hM : MatMulAvailable ω) :
    ∃ (P : TimeSpaceMA.Program) (C c : ℝ) (g : ℕ → ℕ → ℝ), 0 < C ∧ 0 < c ∧ IsSubpoly g ∧
      ∀ (k p : ℕ) (b : ℝ) (N : Matrix (Fin k) (Fin k) ℤ), 1 ≤ k →
        IsUpperUnitri (dyMat N p) → frob (dyMat N p) ≤ (2 : ℝ) ^ b →
        frob (dyMat N p)⁻¹ ≤ (2 : ℝ) ^ b →
        C * (b + k * Real.logb 2 (2 * k) ^ 2) ≤ p →
        SoftmaxAttnFD.DeterministicWithin P (TimeSpaceMA.memOf (natCode p ++ matCode N))
          (fun mem => ∃ U : Matrix (Fin k) (Fin k) ℤ, memHolds mem (matCode U) ∧
            IsUpperUnitri U ∧
            frob (dyMat N p * rmat U) ≤ (2 : ℝ) ^ (c * Real.logb 2 (2 * k) ^ 2) ∧
            frob (dyMat N p * rmat U)⁻¹ ≤ (2 : ℝ) ^ (c * Real.logb 2 (2 * k) ^ 2) ∧
            frob (rmat U) ≤ (2 : ℝ) ^ (b + c * Real.logb 2 (2 * k) ^ 2))
          (g k p * (k : ℝ) ^ ω * p) := by sorry

end LatticeAvgPrec.OneVector
