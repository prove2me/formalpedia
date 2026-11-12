-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_theorem_2_4
-- name    : LatticeAvgPrec.OneVector.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:51:07.48037+00:00
-- url     : https://prove2.me/theorems/f7f2dfda-eac5-4ecf-8866-f53f6626cfde
-- title:
--   Theorem 2.4 — Computing Smith massagers [LS26]
-- statement:
--   Let $\omega$ be an available matrix-multiplication exponent, $2<\omega\le3$. For a nonsingular $H\in\mathbb Z^{n\times n}$ ($n\ge1$) whose row bitlengths sum to $L$, a Las Vegas algorithm computes a reduced Smith massager $(S,F)$ for $H$, $S=\operatorname{diag}(s_1,\dots,s_m)$, in expected
--   $$\widetilde O\bigl(n^{\omega-1}(L+n)\bigr)$$
--   bit operations, input and output included. The output satisfies
--   $$\Lambda(H)=\{p\in\mathbb Z^n: F^Tp\in S\mathbb Z^m\},\qquad \prod_j s_j=|\det H|,$$
--   and the map $F^T:\mathbb Z^n\to\mathbb Z^m/S\mathbb Z^m$ is onto.
--
--   This is the massager computation of Labahn and Storjohann, restated in the column convention; it converts lattice membership in $\Lambda(H)$ into short modular equations in the one-vector algorithm.
--
--   **Formalization Note** One program $P$ and one subpolynomial factor $g(n,L)$ serve all inputs. The output is the code of $(s_1,\dots,s_m)$ followed by the code of $F$.
--
--   Differences from the source:
--   - reading: costs measured in bit operations, with quasi-linear scalar integer arithmetic; Las Vegas expected cost → bit cost of a program of the published logarithmic-cost RAM (TimeSpaceMA_RAM with the cost layer SoftmaxAttnFD_Machine): each instruction costs 1 plus the bit sizes of every address and value it touches; LasVegasWithin: correct on every halting coin tape, expected cost at most the bound; reason: the paper names no machine; the matrix-multiplication hypothesis MatMulAvailable is stated in the same model, so the reading neither adds nor removes power
--   - reading: Õ(f) suppresses subpolynomial factors in the dimension and precision parameters (p.4) → g(n, L)·f with g subpolynomial (IsSubpoly: for every ε > 0, g x y ≤ C_ε (x + y + 2)^ε), g chosen with the program before every input; reason: the p.4 convention made uniform; a factor fixed before the input is the honest reading of Õ
--   - encoding: binary input and output → integers coded one bit per memory cell (natCode / intCode, self-delimiting), vectors and matrices with their dimensions first, input from cell 0 (memOf), output held from cell 0 (memHolds); reason: keeps the bit count of the binary representation; the codes are prefix-free, so the output is read unambiguously
--   - encoding: n×n matrices with an implicit positive dimension → 1 ≤ n; reason: at n = 0 the cost bound is 0 while every run costs at least 1; the 0-dimensional case is degenerate and not considered by the source
--   - encoding: a fixed available matrix-multiplication exponent 2 < ω ≤ 3; multiplying order-n integer matrices with b-bit entries costs Õ(n^ω b) (pp.4, 9) → hypotheses 2 < ω ≤ 3 and MatMulAvailable ω (a coin-free RAM program multiplies such matrices within g₀(n,b)·n^ω·b, g₀ subpolynomial); reason: the paper's standing assumption stated as a hypothesis; ω = 3 satisfies it, so the statement is not vacuous
--   - encoding: S = diag(s_1, …, s_m) → s : Fin m → ℕ, the invariant factors exceeding one in any order (multiset equality), output as vecCode s; reason: the page fixes no order; any order gives a Smith massager
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Theorem 2.4, p. 9

import Definitions.Def_LatticeAvgPrec_OneVector_Cost
open Matrix

namespace LatticeAvgPrec.OneVector

/-- **Theorem 2.4** (Computing Smith massagers [LS26]; Zhou–Wang–Wang, STOC 2027 submission #1574,
p.9). For nonsingular `H ∈ ℤ^{n×n}` whose row bitlengths sum to `L`, a Las Vegas algorithm computes
a reduced Smith massager `(S, F)` for `H` in expected `Õ(n^{ω−1}(L+n))` bit operations. It
satisfies `Λ(H) = {p ∈ ℤ^n : Fᵀp ∈ Sℤ^m}` and `∏_j s_j = |det H|`, and `Fᵀ : ℤ^n → ℤ^m/Sℤ^m` is
onto. -/
theorem theorem_2_4 (ω : ℝ) (hω₁ : 2 < ω) (hω₂ : ω ≤ 3) (hM : MatMulAvailable ω) :
    ∃ (P : TimeSpaceMA.Program) (g : ℕ → ℕ → ℝ), IsSubpoly g ∧
      ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ), 1 ≤ n → H.det ≠ 0 →
        SoftmaxAttnFD.LasVegasWithin P (TimeSpaceMA.memOf (matCode H))
          (fun mem => ∃ (m : ℕ) (s : Fin m → ℕ) (F : Matrix (Fin n) (Fin m) ℤ),
            memHolds mem (vecCode (fun j => (s j : ℤ)) ++ matCode F) ∧
            IsReducedSmithMassager H s F ∧
            lat H = {p : Fin n → ℤ | ∀ j, (s j : ℤ) ∣ (Fᵀ *ᵥ p) j} ∧
            ((∏ j, s j : ℕ) : ℤ) = |H.det| ∧
            ∀ y : Fin m → ℤ, ∃ p : Fin n → ℤ, ∀ j, (s j : ℤ) ∣ (Fᵀ *ᵥ p - y) j)
          (g n (totalRowBits H) * (n : ℝ) ^ (ω - 1) * ((totalRowBits H : ℝ) + n)) := by sorry

end LatticeAvgPrec.OneVector
