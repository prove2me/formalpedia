-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_theorem_2_2
-- name    : LatticeAvgPrec.OneVector.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:51:32.369509+00:00
-- url     : https://prove2.me/theorems/c8cc21b5-d888-442c-b996-51b6e9e8e1e1
-- title:
--   Theorem 2.2 — Average-height HNF [LS26]
-- statement:
--   Let $\omega$ be an available exponent, $2<\omega\le3$. For a nonsingular $B\in\mathbb Z^{n\times n}$ ($n\ge1$) whose row bitlengths sum to $L$, a Las Vegas algorithm computes its upper column Hermite normal form $H$ (Definition 2.1: $\Lambda(H)=\Lambda(B)$, $H$ upper triangular, $H_{ii}>0$, $0\le H_{ij}<H_{ii}$ for $i<j$) in expected
--   $$\widetilde O\bigl(n^{\omega-1}(L+n)\bigr)$$
--   bit operations, input and output included.
--
--   This is the preprocessing step that reduces the general input of Theorem 1.1 to the HNF input of Theorem 3.3 at average-precision cost.
--
--   **Formalization Note** One program and one subpolynomial factor $g(n,L)$ serve all inputs.
--
--   Differences from the source:
--   - reading: costs measured in bit operations, with quasi-linear scalar integer arithmetic; Las Vegas expected cost → bit cost of a program of the published logarithmic-cost RAM (TimeSpaceMA_RAM with the cost layer SoftmaxAttnFD_Machine): each instruction costs 1 plus the bit sizes of every address and value it touches; LasVegasWithin: correct on every halting coin tape, expected cost at most the bound; reason: the paper names no machine; the matrix-multiplication hypothesis MatMulAvailable is stated in the same model, so the reading neither adds nor removes power
--   - reading: Õ(f) suppresses subpolynomial factors in the dimension and precision parameters (p.4) → g(n, L)·f with g subpolynomial (IsSubpoly: for every ε > 0, g x y ≤ C_ε (x + y + 2)^ε), g chosen with the program before every input; reason: the p.4 convention made uniform; a factor fixed before the input is the honest reading of Õ
--   - encoding: binary input and output → integers coded one bit per memory cell (natCode / intCode, self-delimiting), vectors and matrices with their dimensions first, input from cell 0 (memOf), output held from cell 0 (memHolds); reason: keeps the bit count of the binary representation; the codes are prefix-free, so the output is read unambiguously
--   - encoding: n×n matrices with an implicit positive dimension → 1 ≤ n; reason: at n = 0 the cost bound is 0 while every run costs at least 1; the 0-dimensional case is degenerate and not considered by the source
--   - encoding: a fixed available matrix-multiplication exponent 2 < ω ≤ 3; multiplying order-n integer matrices with b-bit entries costs Õ(n^ω b) (pp.4, 9) → hypotheses 2 < ω ≤ 3 and MatMulAvailable ω (a coin-free RAM program multiplies such matrices within g₀(n,b)·n^ω·b, g₀ subpolynomial); reason: the paper's standing assumption stated as a hypothesis; ω = 3 satisfies it, so the statement is not vacuous
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Theorem 2.2, p. 9

import Definitions.Def_LatticeAvgPrec_OneVector_Cost
open Matrix

namespace LatticeAvgPrec.OneVector

/-- **Theorem 2.2** (Average-height HNF [LS26]; STOC 2027 submission #1574, p.9). For nonsingular
`B ∈ ℤ^{n×n}` whose row bitlengths sum to `L`, a Las Vegas algorithm computes its upper column HNF
in expected `Õ(n^{ω−1}(L + n))` bit operations. -/
theorem theorem_2_2 (ω : ℝ) (hω₁ : 2 < ω) (hω₂ : ω ≤ 3) (hM : MatMulAvailable ω) :
    ∃ (P : TimeSpaceMA.Program) (g : ℕ → ℕ → ℝ), IsSubpoly g ∧
      ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ), 1 ≤ n → B.det ≠ 0 →
        SoftmaxAttnFD.LasVegasWithin P (TimeSpaceMA.memOf (matCode B))
          (fun mem => ∃ H : Matrix (Fin n) (Fin n) ℤ, memHolds mem (matCode H) ∧
            IsUpperColHNF B H)
          (g n (totalRowBits B) * (n : ℝ) ^ (ω - 1) * ((totalRowBits B : ℝ) + n)) := by sorry

end LatticeAvgPrec.OneVector
