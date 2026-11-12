-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_corollary_3_4_hnf
-- name    : LatticeAvgPrec.OneVector.corollary_3_4_hnf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:51:25.957047+00:00
-- url     : https://prove2.me/theorems/704d925c-3d77-4306-94db-3497b43a4df2
-- title:
--   Corollary 3.4, HNF-input sentence — fast instantiation (general-input sentence: Theorem 1.1, the goal)
-- statement:
--   Let $\omega$ be an available exponent, $2<\omega\le3$. The conversion of Theorem 3.3 can be implemented in expected $\widetilde O(n^{\omega-1}(\mathcal D+n))$ bit operations: there are a Las Vegas program, a constant $c>0$ and a subpolynomial factor $g$ such that for every $H\in\mathbb Z^{n\times n}$ in HNF ($n\ge1$) with $\mathcal D=\log_2\det H$ the program returns
--   $$0\ne v\in\Lambda(H),\qquad \|v\|_2\le 2^{cn}\lambda_1(\Lambda(H)),\qquad \|v\|_2\le 2^{cn}2^{\mathcal D/n}$$
--   within expected cost $g(n,\lceil\mathcal D\rceil)\,n^{\omega-1}(\mathcal D+n)$, input and output included.
--
--   This is the first sentence of Corollary 3.4; its second sentence, for a general nonsingular basis of total row bitlength $L$ at cost $\widetilde O(n^{\omega-1}(L+n))$, is Theorem 1.1, the goal of this mission. Both parts are to be proved.
--
--   **Formalization Note** The output guarantee is that of Theorem 3.3, which "the conversion" refers to.
--
--   Differences from the source:
--   - reading: costs measured in bit operations, with quasi-linear scalar integer arithmetic; Las Vegas expected cost → bit cost of a program of the published logarithmic-cost RAM (TimeSpaceMA_RAM with the cost layer SoftmaxAttnFD_Machine): each instruction costs 1 plus the bit sizes of every address and value it touches; LasVegasWithin: correct on every halting coin tape, expected cost at most the bound; reason: the paper names no machine; the matrix-multiplication hypothesis MatMulAvailable is stated in the same model, so the reading neither adds nor removes power
--   - reading: Õ(f) suppresses subpolynomial factors in the dimension and precision parameters (p.4) → g(n, ⌈𝒟⌉)·f with g subpolynomial (IsSubpoly: for every ε > 0, g x y ≤ C_ε (x + y + 2)^ε), g chosen with the program before every input; reason: the p.4 convention made uniform; a factor fixed before the input is the honest reading of Õ
--   - encoding: binary input and output → integers coded one bit per memory cell (natCode / intCode, self-delimiting), vectors and matrices with their dimensions first, input from cell 0 (memOf), output held from cell 0 (memHolds); reason: keeps the bit count of the binary representation; the codes are prefix-free, so the output is read unambiguously
--   - encoding: n×n matrices with an implicit positive dimension → 1 ≤ n; reason: at n = 0 the cost bound is 0 while every run costs at least 1; the 0-dimensional case is degenerate and not considered by the source
--   - encoding: a fixed available matrix-multiplication exponent 2 < ω ≤ 3; multiplying order-n integer matrices with b-bit entries costs Õ(n^ω b) (pp.4, 9) → hypotheses 2 < ω ≤ 3 and MatMulAvailable ω (a coin-free RAM program multiplies such matrices within g₀(n,b)·n^ω·b, g₀ subpolynomial); reason: the paper's standing assumption stated as a hypothesis; ω = 3 satisfies it, so the statement is not vacuous
--   - encoding: 2^{O(n)} → 2^(c·n) with c > 0 chosen with the program, before every input; reason: the uniform reading of the O(·) in the exponent
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Corollary 3.4, first sentence, p. 13

import Definitions.Def_LatticeAvgPrec_OneVector_Cost
open Matrix

namespace LatticeAvgPrec.OneVector

/-- **Corollary 3.4**, first sentence (Fast instantiation; STOC 2027 submission #1574, p.13): the
conversion of Theorem 3.3 can be implemented in expected `Õ(n^{ω−1}(D + n))` bit operations. For
`H ∈ ℤ^{n×n}` in HNF with `D = log det H`, a Las Vegas program returns `0 ≠ v ∈ Λ(H)` with
`‖v‖₂ ≤ 2^{O(n)} λ₁(Λ(H))` and `‖v‖₂ ≤ 2^{O(n)} 2^{D/n}`. The second sentence (general input) is
Theorem 1.1, the mission's goal. -/
theorem corollary_3_4_hnf (ω : ℝ) (hω₁ : 2 < ω) (hω₂ : ω ≤ 3) (hM : MatMulAvailable ω) :
    ∃ (P : TimeSpaceMA.Program) (c : ℝ) (g : ℕ → ℕ → ℝ), 0 < c ∧ IsSubpoly g ∧
      ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ), 1 ≤ n → IsHNF H →
        SoftmaxAttnFD.LasVegasWithin P (TimeSpaceMA.memOf (matCode H))
          (fun mem => ∃ v : Fin n → ℤ, memHolds mem (vecCode v) ∧ HNFVecGood c H v)
          (g n ⌈Real.logb 2 (H.det : ℝ)⌉₊ * (n : ℝ) ^ (ω - 1) *
            (Real.logb 2 (H.det : ℝ) + n)) := by sorry

end LatticeAvgPrec.OneVector
