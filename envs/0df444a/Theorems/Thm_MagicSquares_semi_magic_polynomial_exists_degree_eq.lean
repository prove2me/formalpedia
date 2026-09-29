-- Prove2me | Theorems.Thm_MagicSquares_semi_magic_polynomial_exists_degree_eq
-- name    : MagicSquares.semi_magic_polynomial_exists_degree_eq
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-20T02:29:29.227899+00:00
-- url     : https://prove2.me/theorems/4394b225-cc88-46d4-a57e-0765707d3246
-- title:
--   Theorem 1 (i) with the exact degree, for positive line sums (Spencer's elementary route, formalised)
-- statement:
--   **Spencer's theorem with the exact degree.**
--
--   Write $H_{n}(t)$ for the number of $n\times n$ arrays of nonnegative integers whose every row
--   and every column sums to $t$. The theorem states that for every order $n\ge 1$ there is a
--   rational polynomial $p$ of degree *exactly* $(n-1)^{2}$ such that
--
--   $$p(t)=H_{n}(t)\qquad\text{for every }t\ge 1 .$$
--
--   **Why the degree is $(n-1)^{2}$.** It is the dimension of the Birkhoff polytope $B_{n}$, and
--   $H_{n}(t)$ is its Ehrhart polynomial, so the value is forced by the BCCG Theorem 1. The proof
--   given here is nevertheless *elementary* and uses no Ehrhart theory and no lattice-point
--   machinery. It follows J. Spencer, *Counting magic squares*, Amer. Math. Monthly **87** (1980)
--   397-399: generating functions, Hall's marriage theorem, and the finite poset of **supports**
--   $B(T)=\{(i,j):T(i,j)\ge 1\}$ ordered by inclusion.
--
--   1. *Partial fractions, discretely.* If a sequence satisfies a triangular recurrence with
--      polynomial coefficients of degree $\le K$, telescoping it against the discrete
--      antiderivative $\sum_{m<n}m^{d}$ (Faulhaber, in Bernoulli-polynomial form) exhibits it as a
--      polynomial of degree $\le K+1$.
--   2. *Poset recursion.* Birkhoff-von Neumann attaches to each support $B$ a permutation
--      $\sigma$ with $\varphi(\sigma)\subseteq B$, and splitting $T\mapsto T-P$ off a square of
--      line sum $s$ gives $h_{B}(s)=h_{B}(s-1)+\sum_{C}h_{C}(s-1)$ over the candidates
--      $B\setminus\varphi(\sigma)\subseteq C\subsetneq B$. Strong induction on $|B|$ then makes
--      each level count a polynomial.
--   3. *Aggregation.* The support fibres partition the semi-magic squares, so $t\mapsto H_{n}(t)$
--      agrees with a polynomial for $t\ge 1$.
--   4. *Degree, both ways.* The upper bound $(n-1)^{2}$ is measured by the rank
--      $\rho(B)=\dim\{M:\text{line sums }0,\ \operatorname{supp}M\subseteq B\}$, which strictly
--      increases along proper inclusions of supports. The lower bound is explicit: for order $n+1$
--      and line sum $(n+1)s$, put a free block $c:\mathrm{Fin}\,n\to\mathrm{Fin}\,n\to
--      \mathrm{Fin}(s/n+1)$ in the top-left $n\times n$ corner and let the line-sum equations fill
--      in the last row, last column and corner,
--      $$M_{pq}=s+c_{pq},\quad M_{p,\mathrm{last}}=s-\textstyle\sum_{q}c_{pq},\quad
--        M_{\mathrm{last},q}=s-\textstyle\sum_{p}c_{pq},\quad
--        M_{\mathrm{last},\mathrm{last}}=s+\textstyle\sum_{p,q}c_{pq},$$
--      which is injective and gives $H_{n+1}\bigl((n+1)s\bigr)\ge (s/n+1)^{n^{2}}$.
--
--   **What is *not* claimed.** Agreement at $t=0$. The support-set recursion only ever sees
--   *positive* line sums - the squares of line sum $0$ have empty support and the recursion has no
--   term for it - so the value $p(0)=H_{n}(0)=1$ is out of reach of this route. That value is
--   exactly Ehrhart-Macdonald reciprocity at $-1$, i.e. the statement that $B_{n}$ has no interior
--   lattice points for $n\ge 2$, and it is the separate rung `semi_magic_reciprocity`. The
--   mission goal `semi_magic_polynomial_exists` quantifies over **all** $t:\mathbb{N}$ and is
--   therefore strictly stronger than this node.
-- source:
--   J. Spencer, Counting magic squares, Amer. Math. Monthly 87 (1980), 397--399; M. Beck and D. Pixton, The Ehrhart polynomial of the Birkhoff polytope, Discrete Comput. Geom. 30 (2003), 623--637 (arXiv:math/0202267); E. Ehrhart, Sur les polyedres rationnels homothetiques a n dimensions, C. R. Acad. Sci. Paris 254 (1962), 616--618.

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem semi_magic_polynomial_exists_degree_eq (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ, p.natDegree = (n - 1) ^ 2 ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  sorry

end MagicSquares
