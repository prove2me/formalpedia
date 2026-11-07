-- Prove2me | Theorems.Thm_MinrankTW_proposition_1
-- name    : MinrankTW.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:09.275212+00:00
-- url     : https://prove2.me/theorems/877e045a-ac8e-474d-ac6c-44737ee4bb16
-- title:
--   Proposition 1 — a join takes $O_q((b+1)^2N_q(b))$ coefficient operations and $N_q(b)\,\mathrm{poly}$ time
-- statement:
--   For $b=a+c$, consider the join $h(R)=\sum_{R_1\boxplus R_2=R}f(R_1)g(R_2)$ of two tables on the linear relations in $\mathbb F_q^a\oplus\mathbb F_q^c$. The source states: a join takes $O_q((b+1)^2N_q(b))$ coefficient operations and $N_q(b)\,\mathrm{poly}(b)$ indexing time; integer polynomial tables add only a polynomial factor in the degree and the coefficient bit length. Precisely:
--
--   1. there is a constant $C$ depending only on $\mathbb F_q$ such that for all $a,c$ a straight-line program with at most $C(b+1)^2N_q(b)$ arithmetic operations computes $h$ from the entries of $f$ and $g$ over every commutative ring in which $p=\mathrm{char}\,\mathbb F_q$ is invertible;
--   2. there are a logarithmic-cost RAM program and constants $C,k$ depending only on $\mathbb F_q$ and its encoding such that, for all $a,c,d,H$ and all integer polynomial tables $f,g$ of degree at most $d$ with coefficients of absolute value at most $H$, stored in the record layout, the program writes $h$ (degree at most $2d$) in the same layout at total cost at most
--   $$
--   C\,N_q(b)\,\bigl(b+d+\ell(H)+1\bigr)^k,\qquad \ell(H)=\mathrm{size}(H)+1 .
--   $$
--
--   **Formalization Note** In clause 1 the inputs are indexed by $(\mathrm{false},R)$ for $f(R)$ and $(\mathrm{true},R)$ for $g(R)$. In clause 2 the table of $g$ starts right after that of $f$ and all later cells are $0$.
--
--   Differences from the source:
--   - encoding: "O_q((b+1)²N_q(b)) coefficient operations" → a straight-line program per (a, c) with at most C(b+1)²N_q(b) arithmetic gates over every commutative ring with p invertible; reason: the coefficient-operation model of the source (cf. Theorem 4)
--   - reading: "N_q(b) poly(b) indexing time" and "integer polynomial tables add only a polynomial factor in the degree and coefficient bit length" → one total-cost bound C·N_q(b)·(b + d + ℓ(H) + 1)^k for a logarithmic-cost RAM run on integer tables; reason: a RAM run has one cost; the source's time for integer tables is its coefficient work times a polynomial in d and ℓ(H) plus N_q(b)poly(b) indexing, which is a bound of this form, and the split between the two parts is not an observable of the run
--   - encoding: tables given to the algorithm → a record layout listing each relation once by a spanning matrix (any order) followed by signed coefficients; reason: an input encoding that presupposes no canonical subspace enumeration
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Proposition 1, p.15 (with Sections A.1–A.3, pp.16–17)

import Mathlib
import Definitions.Def_MinrankTW_Nq
import Definitions.Def_MinrankTW_joinConv
import Definitions.Def_MinrankTW_SLP
import Definitions.Def_MinrankTW_RAM
import Definitions.Def_MinrankTW_joinTableLayout

namespace MinrankTW

open Polynomial

/-- **Proposition 1** (Cost of a join), Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), p.15. For `b = a + c`, a join
`h(R) = ∑_{R₁ ⊞ R₂ = R} f(R₁) g(R₂)` of two tables on the linear relations in `F^a ⊕ F^c` takes
`O_q((b + 1)² N_q(b))` coefficient operations and `N_q(b) poly(b)` indexing time; integer
polynomial tables add only a polynomial factor in the degree and coefficient bit length.
1. Coefficient operations: for each `a, c` a straight-line program with at most
   `C (b + 1)² N_q(b)` operations (`C` depending only on `F`) computes `h` from the entries of
   `f` and `g` over every commutative ring in which `p = char F` is invertible.
2. Total time for integer polynomial tables: one logarithmic-cost RAM program which, on two tables
   of degree at most `d` with coefficients of absolute value at most `H`, stored in the record
   layout, writes `h` (degree at most `2d`) in the same layout at total cost
   `≤ C N_q(b) (b + d + ℓ(H) + 1)^k`, `C, k` depending only on `F` and its encoding `e`.

**Formalization Note** In clause 1 the program's inputs are indexed by `(false, R)` (the entry
`f(R)`) and `(true, R)` (the entry `g(R)`), its outputs by `R`. In clause 2 the input memory
holds the table of `f` from cell `0` and that of `g` right after it (cell
`4 + N_q(b)·recLen a c d`), all later cells being `0`; `ℓ(H) = size(H) + 1`. The bound in
clause 2 contains both the coefficient work and the indexing time. -/
theorem proposition_1 (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (e : F ≃ Fin (Fintype.card F)) :
    (∃ C : ℕ, ∀ a c : ℕ, ∃ P : SLP (Bool × Submodule F ((Fin a → F) × (Fin c → F)))
        (Submodule F ((Fin a → F) × (Fin c → F))),
      P.WellFormed ∧ P.cost ≤ C * (a + c + 1) ^ 2 * Nq F (a + c) ∧
      ∀ (A : Type) [CommRing A] (pinv : A), (ringChar F : A) * pinv = 1 →
        ∀ f g : Submodule F ((Fin a → F) × (Fin c → F)) → A,
          P.eval pinv (fun ix => if ix.1 then g ix.2 else f ix.2) = joinConv f g) ∧
    (∃ (P : List Instr) (C k : ℕ), ∀ (a c d H : ℕ)
        (f g : Submodule F ((Fin a → F) × (Fin c → F)) → ℤ[X]) (mem : ℕ → ℕ),
      (∀ R, (f R).natDegree ≤ d) → (∀ R, (g R).natDegree ≤ d) →
      (∀ R i, |(f R).coeff i| ≤ (H : ℤ)) → (∀ R i, |(g R).coeff i| ≤ (H : ℤ)) →
      EncodesTableAt e mem 0 a c d f →
      EncodesTableAt e mem (4 + Nq F (a + c) * recLen a c d) a c d g →
      (∀ k', 2 * (4 + Nq F (a + c) * recLen a c d) ≤ k' → mem k' = 0) →
      HaltsWithin P mem (C * Nq F (a + c) * (a + c + d + logLen H + 1) ^ k)
        (fun out => EncodesTableAt e out 0 a c (2 * d) (joinConv f g))) := by sorry

end MinrankTW
