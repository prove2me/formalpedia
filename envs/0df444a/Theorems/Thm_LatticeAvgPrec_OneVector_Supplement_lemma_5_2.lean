-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_Supplement_lemma_5_2
-- name    : LatticeAvgPrec.OneVector.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:43:28.594091+00:00
-- url     : https://prove2.me/theorems/6e905527-2abe-4e78-a4bf-c5c4e226d3b0
-- title:
--   Lemma 5.2 — Partial linearization
-- statement:
--   For $X,Y\in\mathbb Z^{n\times n}$, $n\ge1$, put
--
--   $$
--   a_i=\max_k\mathrm{bits}(X_{ik}),\qquad b_j=\max_k\mathrm{bits}(Y_{kj}),\qquad S=\sum_ia_i+\sum_jb_j,\qquad w=\lceil S/n\rceil .
--   $$
--
--   There are two deterministic programs $\mathcal P_1,\mathcal P_2$ and one subpolynomial factor $g$ such that for all $n$, $X$, $Y$ there are integer matrices $X'\in\mathbb Z^{r\times n}$ and $Y'\in\mathbb Z^{n\times c}$ with $r+c\le3n$ and every entry of magnitude less than $2^w$, such that
--
--   1. on input $(X,Y)$, $\mathcal P_1$ outputs $(X',Y')$;
--   2. on input $(a,b,X'Y')$, $\mathcal P_2$ outputs $XY$;
--
--   each within $g(n,S)\,nS$ bit operations, input and output included.
--
--   The lemma balances the operands of an integer matrix product so that every entry has the average bitlength $S/n$; Theorem 5.1 uses it to keep the lattice weights of its encoding at that scale.
--
--   **Formalization Note** $\mathcal P_2$ does not see $X$ and $Y$, only their row and column bit profiles $a,b$ (which fix the digit layout) and the product $X'Y'$. $S$ is the published total row bitlength of $X$ plus that of $Y^{\mathsf T}$; $w$ is $\lfloor (S+n-1)/n\rfloor$. $\widetilde O$ follows the conventions of §1.1.1 (p.4), with $g$ chosen with the programs before every input.
--
--   Differences from the source:
--   - reading: "Scalar work costing Õ(nS) converts XY to a product X′Y′ … and recovers the product XY from X′Y′" → two coin-free programs: (X, Y) ↦ (X′, Y′), and (a, b, X′Y′) ↦ XY, each within g(n, S)·n·S; reason: the recovery uses only the digit layout, which a and b determine; the recovering program does not see X and Y
--   - encoding: w = ⌈S/n⌉ → (S + n − 1)/n in ℕ; reason: ceiling division for n ≥ 1
--   - encoding: X, Y ∈ ℤ^{n×n} → 1 ≤ n; reason: excludes the empty product, where the bound is 0
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Lemma 5.2 and (20), pp.20–21 (proof p.21)

import Definitions.Def_LatticeAvgPrec_OneVector_Supplement_Objects
open Matrix

namespace LatticeAvgPrec.OneVector.Supplement

/-- **Lemma 5.2** (Partial linearization; STOC 2027 submission #1574, p.21). For `X, Y ∈ ℤ^{n×n}`
with `a_i = max_k bits(X_ik)`, `b_j = max_k bits(Y_kj)`, `S = Σ_i a_i + Σ_j b_j` (20), set
`w = ⌈S/n⌉`. Scalar work costing `Õ(nS)` converts `XY` to a product `X'Y'` of integer matrices of
sizes `r × n` and `n × c`, with `r + c ≤ 3n`, and recovers the product `XY` from `X'Y'`. Every entry
of `X'` and `Y'` has magnitude less than `2^w`.

**Formalization Note** Two coin-free programs and one subpolynomial factor `g(n, S)` are chosen
before the input. The first reads `(X, Y)` and writes `(X', Y')`. The second reads only the bit
profiles `a, b` and the product `X'Y'`, and writes `XY`. `S` is
`totalRowBits X + totalRowBits Yᵀ`. -/
theorem lemma_5_2 :
    ∃ (P₁ P₂ : TimeSpaceMA.Program) (g : ℕ → ℕ → ℝ), IsSubpoly g ∧
      ∀ (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℤ), 1 ≤ n →
        ∃ (r c : ℕ) (X' : Matrix (Fin r) (Fin n) ℤ) (Y' : Matrix (Fin n) (Fin c) ℤ),
          r + c ≤ 3 * n ∧
          (∀ i j, |X' i j| < 2 ^ ((totalRowBits X + totalRowBits Yᵀ + n - 1) / n)) ∧
          (∀ i j, |Y' i j| < 2 ^ ((totalRowBits X + totalRowBits Yᵀ + n - 1) / n)) ∧
          SoftmaxAttnFD.DeterministicWithin P₁ (TimeSpaceMA.memOf (matCode X ++ matCode Y))
            (fun mem => memHolds mem (matCode X' ++ matCode Y'))
            (g n (totalRowBits X + totalRowBits Yᵀ) * n *
              ((totalRowBits X + totalRowBits Yᵀ : ℕ) : ℝ)) ∧
          SoftmaxAttnFD.DeterministicWithin P₂
            (TimeSpaceMA.memOf (vecCode (fun i => (rowBits X i : ℤ)) ++
              vecCode (fun j => (rowBits Yᵀ j : ℤ)) ++ matCode (X' * Y')))
            (fun mem => memHolds mem (matCode (X * Y)))
            (g n (totalRowBits X + totalRowBits Yᵀ) * n *
              ((totalRowBits X + totalRowBits Yᵀ : ℕ) : ℝ)) := by sorry

end LatticeAvgPrec.OneVector.Supplement
