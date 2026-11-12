-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_theorem_1_1
-- name    : LatticeAvgPrec.OneVector.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:51:51.558193+00:00
-- url     : https://prove2.me/theorems/bd270ede-8d2f-4557-9d2f-082c016ef3bd
-- title:
--   Theorem 1.1 — One short vector: $0\ne v\in\Lambda(B)$, $\|v\|_2\le 2^{O(n)}\lambda_1$, expected $\widetilde O(n^\omega(L/n+1))$
-- statement:
--   Fix an available matrix-multiplication exponent $2<\omega\le3$. There are a Las Vegas algorithm, a constant $c>0$ and a subpolynomial factor $g$ such that, given a nonsingular $B\in\mathbb Z^{n\times n}$ ($n\ge1$) with total row bitlength $L$, the algorithm computes
--   $$0\ne v\in\Lambda(B),\qquad \|v\|_2\le 2^{cn}\lambda_1(\Lambda(B))$$
--   in expected
--   $$g(n,L)\cdot n^{\omega-1}(L+n)=g(n,L)\cdot n^{\omega}\Bigl(\frac Ln+1\Bigr)$$
--   bit operations, input and output included; correctness holds on every halting run.
--
--   Here $\Lambda(B)=B\mathbb Z^n$, $\lambda_1$ is its shortest nonzero length, and $L=\sum_i\max_j\operatorname{bits}(B_{ij})$. The cost follows the average row bitlength $L/n$ rather than the maximum entry size, which is what makes the result useful for bases with a few long rows, such as those of LLL polynomial factorization.
--
--   **Formalization Note** The program, $c$ and $g$ are chosen after $\omega$ and before the input. The formal content is the second sentence of Corollary 3.4 (p.13) with the output guarantee of Theorem 3.3.
--
--   Differences from the source:
--   - reading: costs measured in bit operations, with quasi-linear scalar integer arithmetic; Las Vegas expected cost → bit cost of a program of the published logarithmic-cost RAM (TimeSpaceMA_RAM with the cost layer SoftmaxAttnFD_Machine): each instruction costs 1 plus the bit sizes of every address and value it touches; LasVegasWithin: correct on every halting coin tape, expected cost at most the bound; reason: the paper names no machine; the matrix-multiplication hypothesis MatMulAvailable is stated in the same model, so the reading neither adds nor removes power
--   - reading: Õ(f) suppresses subpolynomial factors in the dimension and precision parameters (p.4) → g(n, L)·f with g subpolynomial (IsSubpoly: for every ε > 0, g x y ≤ C_ε (x + y + 2)^ε), g chosen with the program before every input; reason: the p.4 convention made uniform; a factor fixed before the input is the honest reading of Õ
--   - encoding: binary input and output → integers coded one bit per memory cell (natCode / intCode, self-delimiting), vectors and matrices with their dimensions first, input from cell 0 (memOf), output held from cell 0 (memHolds); reason: keeps the bit count of the binary representation; the codes are prefix-free, so the output is read unambiguously
--   - encoding: n×n matrices with an implicit positive dimension → 1 ≤ n; reason: at n = 0 the cost bound is 0 while every run costs at least 1; the 0-dimensional case is degenerate and not considered by the source
--   - encoding: a fixed available matrix-multiplication exponent 2 < ω ≤ 3; multiplying order-n integer matrices with b-bit entries costs Õ(n^ω b) (pp.4, 9) → hypotheses 2 < ω ≤ 3 and MatMulAvailable ω (a coin-free RAM program multiplies such matrices within g₀(n,b)·n^ω·b, g₀ subpolynomial); reason: the paper's standing assumption stated as a hypothesis; ω = 3 satisfies it, so the statement is not vacuous
--   - encoding: 2^{O(n)} → 2^(c·n) with c > 0 chosen with the program, before every input; reason: the uniform reading of the O(·) in the exponent
--   - encoding: Õ(n^ω(L/n + 1)) → g(n, L)·n^(ω−1)·(L + n); reason: the two expressions are equal for n ≥ 1
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Theorem 1.1 (p.4); formal form Corollary 3.4, second sentence (p.13), with Theorem 3.3 (p.12)

import Definitions.Def_LatticeAvgPrec_OneVector_Cost
open Matrix

namespace LatticeAvgPrec.OneVector

/-- **Theorem 1.1** (One short vector; STOC 2027 submission #1574, p.4; formal form Corollary 3.4,
p.13). Given a nonsingular `B ∈ ℤ^{n×n}` with total row bitlength `L`, a Las Vegas algorithm
computes `0 ≠ v ∈ Λ(B)` with `‖v‖₂ ≤ 2^{O(n)} λ₁` in expected `Õ(n^ω(L/n + 1))` bit operations,
input and output included.

**Formalization Note** `n^ω(L/n + 1) = n^{ω−1}(L + n)`. The program `P`, the constant `c` of
`2^{O(n)}` and the subpolynomial factor `g(n, L)` of `Õ` are chosen after `ω` and before the
input. -/
theorem theorem_1_1 (ω : ℝ) (hω₁ : 2 < ω) (hω₂ : ω ≤ 3) (hM : MatMulAvailable ω) :
    ∃ (P : TimeSpaceMA.Program) (c : ℝ) (g : ℕ → ℕ → ℝ), 0 < c ∧ IsSubpoly g ∧
      ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ), 1 ≤ n → B.det ≠ 0 →
        SoftmaxAttnFD.LasVegasWithin P (TimeSpaceMA.memOf (matCode B))
          (fun mem => ∃ v : Fin n → ℤ, memHolds mem (vecCode v) ∧
            v ≠ 0 ∧ v ∈ lat B ∧ ivNorm v ≤ (2 : ℝ) ^ (c * n) * lam (lat B) 1)
          (g n (totalRowBits B) * (n : ℝ) ^ (ω - 1) * ((totalRowBits B : ℝ) + n)) := by sorry

end LatticeAvgPrec.OneVector
