-- Prove2me | Theorems.Thm_NCQuadLB_coeffX_pal
-- name    : NCQuadLB.coeffX_pal
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:03.237207+00:00
-- url     : https://prove2.me/theorems/0eda4d7c-34fe-4cee-9dce-c03db339fec6
-- title:
--   The coefficient space of $\mathrm{Pal}_{n,d}$: $\mathrm{Coeff}_X(\mathrm{Pal}_{n,d})$ is the set of degree-$d$ $X$-monomials, of span dimension $n^d$
-- statement:
--   Let $\mathbb F$ be a field, $n\ge0$ and $d\ge1$. For $f=\mathrm{Pal}_{n,d}(X,Y)$:
--
--   1. $\mathrm{Coeff}_X(f)$ is exactly the set of all degree-$d$ monomials $x_{i_1}\cdots x_{i_d}$ in the variables $X$;
--   2. $$\dim_{\mathbb F}\mathrm{span}\{\mathrm{Coeff}_X(\mathrm{Pal}_{n,d}(X,Y))\}=n^d.$$
--
--   This is the lower bound on the complexity measure that every circuit for $\mathrm{Pal}_{n,d}$ must match.
--
--   **Formalization Note** $\mathbb F\langle X\rangle$ sits inside $\mathbb F\langle X,Y\rangle$ as the polynomials in the $X$-variables; the dimension is that of the $\mathbb F$-span inside $\mathbb F\langle X,Y\rangle$.
--
--   Differences from the source:
--
--   - reading: no range of $d$ stated in §2 → $d\ge1$; reason: the display is used under Theorem 4.2's standing $d\ge1$; at $d=0$, $\mathrm{Pal}_{n,0}=1$ has $\mathrm{Coeff}_X=\emptyset$, of dimension $0\ne n^0$
--   - encoding: $\mathbb F\langle X,Y\rangle$ with $x_1,\dots,x_n$, $y_1,\dots,y_n$ → the free algebra on $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$, $x_j$ the left and $y_j$ the right copy of $j$, indices from $0$; reason: a renaming of the variables
--   - encoding: $\mathbb F\langle X\rangle$ → the polynomials of $\mathbb F\langle X,Y\rangle$ in the $X$-variables only; spans are taken inside $\mathbb F\langle X,Y\rangle$; reason: $\mathbb F\langle X\rangle\to\mathbb F\langle X,Y\rangle$ is an injective algebra map, so spans and dimensions agree
--   - encoding: $\mathrm{coeff}_m(f)$ defined for $X,Y$-separated $f$ → $\mathrm{coeff}_m(f)=\sum_{u\in X\text{-words}}[u\,m]f\cdot u$ for every $f$; reason: on separated $f$ this is the source's $c_m$; it is applied only to separated polynomials here
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), §2, p.4 ("For f = Pal_{n,d}(X, Y), the set Coeff_X(f) is exactly …")

import Mathlib
import Definitions.Def_NCQuadLB_pal
import Definitions.Def_NCQuadLB_CoeffX

namespace NCQuadLB

/-- **The coefficient space of the palindrome polynomial** (Shastri, Willumsgaard, *A Quadratic Lower Bound for Noncommutative Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, §2, p.4). For
`f = Pal_{n,d}(X, Y)`, the set `Coeff_X(f)` is exactly the set of all degree `d` monomials in the
variables `X`, and `dim_F span{Coeff_X(Pal_{n,d}(X, Y))} = n^d`.

**Formalization Note** `d ≥ 1` is assumed (the standing hypothesis of Theorem 4.2, where this display
is used); at `d = 0`, `Pal_{n,0} = 1` and `Coeff_X(1) = ∅`. The degree `d` monomials in `X` are the
`x_{i_1} ⋯ x_{i_d}` (`xMonomial i`) for `i : Fin d → Fin n`. -/
theorem coeffX_pal {F : Type*} [Field F] (n d : ℕ) (hd : 1 ≤ d) :
    CoeffX (pal F n d) = Set.range (fun i : Fin d → Fin n => xMonomial F i) ∧
      Module.finrank F (Submodule.span F (CoeffX (pal F n d))) = n ^ d := by sorry

end NCQuadLB
