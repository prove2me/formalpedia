-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_Supplement_theorem_5_1
-- name    : LatticeAvgPrec.OneVector.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:43:59.226867+00:00
-- url     : https://prove2.me/theorems/aecd3902-1e33-4fdd-98a9-9e7c2fbcb7b9
-- title:
--   Theorem 5.1 — Matrix multiplication via lattice reduction
-- statement:
--   Fix $\kappa\ge2$. For an order-$r$ integer basis $A$ let $L(A)$ be its total row bitlength, and for $X,Y\in\mathbb Z^{n\times n}$ let $S$ be as in (20): the sum of the row bitlengths of $X$ and the column bitlengths of $Y$.
--
--   1. **Complete bases.** Suppose a program $\mathcal A$ of the logarithmic-cost RAM with coin flips, a constant $c>0$ and a subpolynomial factor $g$ are such that, for every $r\ge1$ and every nonsingular $A\in\mathbb Z^{r\times r}$, $\mathcal A$ is Las Vegas on input $A$ and returns a basis $Z$ of $\Lambda(A)$ with $\|Z_i\|_2\le2^{cr}\lambda_i(\Lambda(A))$ for all $i$, in expected $g(r,L(A))\,r^{\kappa-1}(L(A)+r^2)$ bit operations.
--   2. **Bounded short-span extraction.** Or suppose $\mathcal A$, $c$, $g$ are such that, for every $r\ge1$, every nonsingular $A\in\mathbb Z^{r\times r}$ and every integer radius $B\ge1$, $\mathcal A$ is Las Vegas on input $(A,B)$ and returns an output of Definition 4.5 for $\Lambda(A)$ at radius $B$ with constant $c$, in expected $g(r,L(A)+\mathrm{bits}(B))\,r^{\kappa-1}(L(A)+r\,\mathrm{bits}(B)+r^2)$ bit operations.
--
--   In either case there are a program $\mathcal Q$ and a subpolynomial factor $g'$ such that for every $n\ge1$ and all $X,Y\in\mathbb Z^{n\times n}$, $\mathcal Q$ is Las Vegas on input $(X,Y)$, outputs $XY$, and runs in expected
--
--   $$
--   g'(n,S)\,n^{\kappa-1}\bigl(S+n^2\bigr)
--   $$
--
--   bit operations, input and output included.
--
--   The informal Theorem 1.3 (p.5) is part 1. With $\kappa=\omega$ the reduction shows that the complete-basis bound of Theorem 4.1 is near-optimal relative to integer matrix multiplication when the average precision is $\Omega(n)$: any improvement of its dimension exponent would improve integer matrix multiplication.
--
--   **Formalization Note** Each hypothesis is an existential statement about a program of the same RAM, with its own constant and subpolynomial factor, required on every nonsingular input; $\mathcal Q$ may call it as a subroutine. $S$ is the published total row bitlength of $X$ plus that of $Y^{\mathsf T}$. No matrix-multiplication exponent enters.
--
--   Differences from the source:
--   - reading: "a Las Vegas algorithm returns a complete basis with indexed 2^{O(r)} λ_i quality in expected Õ(r^{κ−1}(L(A)+r²))" → ∃ program, c > 0 and subpolynomial g with LasVegasWithin on every nonsingular A, bound g(r, L(A)) r^{κ−1}(L(A)+r²); reason: the hypothesis constants are fixed by the hypothesis; the Õ convention of §1.1.1
--   - generalization: bounded short-span extraction (Definition 4.5, radius B ≥ 1) at expected Õ(r^{κ−1}(L(A)+r bits(B)+r²)) → the hypothesised algorithm is required only on integer radii B ≥ 1, input (A, B); reason: a weaker hypothesis makes the implication stronger; an algorithm for all radii B ≥ 1 is in particular one for integer radii, and bits(B) is defined for integers
--   - reading: "X, Y can be multiplied in expected Õ(n^{κ−1}(S+n²))" → ∃ program Q and subpolynomial g′ with LasVegasWithin on (X, Y), output the code of XY, bound g′(n, S) n^{κ−1}(S+n²); reason: the Õ convention of §1.1.1; costs include input and output
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Theorem 5.1, p.20 (informal Theorem 1.3, p.5; proof pp.21–22)

import Definitions.Def_LatticeAvgPrec_OneVector_Supplement_Objects
open Matrix

namespace LatticeAvgPrec.OneVector.Supplement

/-- **Theorem 5.1** (Matrix multiplication via lattice reduction; STOC 2027 submission #1574, p.20;
informal form Theorem 1.3, p.5). Fix `κ ≥ 2`, and let `L(A)` be the total row bitlength of an
order-`r` integer basis `A`. Suppose a Las Vegas algorithm returns a complete basis with indexed
`2^{O(r)} λ_i` quality in expected `Õ(r^{κ−1}(L(A) + r²))` bit operations. Then `X, Y ∈ ℤ^{n×n}` can
be multiplied in expected `Õ(n^{κ−1}(S + n²))` bit operations, `S` as in (20). The same conclusion
holds for bounded short-span extraction (Definition 4.5) at expected cost
`Õ(r^{κ−1}(L(A) + r bits(B) + r²))`.

**Formalization Note** Two implications. In each hypothesis the algorithm is a program of the
same RAM, and its constant `c` and subpolynomial factor `g` are those of the hypothesis; it must
work on every nonsingular `A ∈ ℤ^{r×r}` (and, in (b), every integer radius `B ≥ 1`). The
multiplication program `Q` and its subpolynomial factor are the conclusion.
`S = totalRowBits X + totalRowBits Yᵀ`. -/
theorem theorem_5_1 (κ : ℝ) (hκ : 2 ≤ κ) :
    ((∃ (A : TimeSpaceMA.Program) (c : ℝ) (g : ℕ → ℕ → ℝ), 0 < c ∧ IsSubpoly g ∧
        ∀ (r : ℕ) (Am : Matrix (Fin r) (Fin r) ℤ), 1 ≤ r → Am.det ≠ 0 →
          SoftmaxAttnFD.LasVegasWithin A (TimeSpaceMA.memOf (matCode Am))
            (fun mem => ∃ Z : Matrix (Fin r) (Fin r) ℤ, memHolds mem (matCode Z) ∧
              lat Z = lat Am ∧
              ∀ i : Fin r, colNorm Z i ≤ (2 : ℝ) ^ (c * r) * lam (lat Am) ((i : ℕ) + 1))
            (g r (totalRowBits Am) * (r : ℝ) ^ (κ - 1) *
              ((totalRowBits Am : ℝ) + (r : ℝ) ^ 2))) →
      ∃ (Q : TimeSpaceMA.Program) (g' : ℕ → ℕ → ℝ), IsSubpoly g' ∧
        ∀ (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℤ), 1 ≤ n →
          SoftmaxAttnFD.LasVegasWithin Q (TimeSpaceMA.memOf (matCode X ++ matCode Y))
            (fun mem => memHolds mem (matCode (X * Y)))
            (g' n (totalRowBits X + totalRowBits Yᵀ) * (n : ℝ) ^ (κ - 1) *
              (((totalRowBits X + totalRowBits Yᵀ : ℕ) : ℝ) + (n : ℝ) ^ 2))) ∧
    ((∃ (A : TimeSpaceMA.Program) (c : ℝ) (g : ℕ → ℕ → ℝ), 0 < c ∧ IsSubpoly g ∧
        ∀ (r : ℕ) (Am : Matrix (Fin r) (Fin r) ℤ) (B : ℕ), 1 ≤ r → Am.det ≠ 0 → 1 ≤ B →
          SoftmaxAttnFD.LasVegasWithin A (TimeSpaceMA.memOf (matCode Am ++ natCode B))
            (fun mem => ∃ (k : ℕ) (X : Matrix (Fin r) (Fin k) ℤ), memHolds mem (matCode X) ∧
              IsShortSpanExt c r ((fun z : Fin r → ℤ => fun t => ((z t : ℤ) : ℝ)) '' lat Am) B
                (fun i => fun t => ((X t i : ℤ) : ℝ)))
            (g r (totalRowBits Am + bits (B : ℤ)) * (r : ℝ) ^ (κ - 1) *
              ((totalRowBits Am : ℝ) + r * bits (B : ℤ) + (r : ℝ) ^ 2))) →
      ∃ (Q : TimeSpaceMA.Program) (g' : ℕ → ℕ → ℝ), IsSubpoly g' ∧
        ∀ (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℤ), 1 ≤ n →
          SoftmaxAttnFD.LasVegasWithin Q (TimeSpaceMA.memOf (matCode X ++ matCode Y))
            (fun mem => memHolds mem (matCode (X * Y)))
            (g' n (totalRowBits X + totalRowBits Yᵀ) * (n : ℝ) ^ (κ - 1) *
              (((totalRowBits X + totalRowBits Yᵀ : ℕ) : ℝ) + (n : ℝ) ^ 2))) := by sorry

end LatticeAvgPrec.OneVector.Supplement
