-- Prove2me | Theorems.Thm_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof
-- name    : ModularCurve.hasPrincipalDivisors_charLDegeneracyRoof
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/1da51625-4b73-5414-8abc-96d8e19466d3
-- title:
--   Principal divisors on the degeneracy roof k(̃ j,̃ j_N,̃ j_q,̃ j_{Nq})
-- statement:
--   Let $k$ be a field, let $N \ge 1$ be a natural number and let $q$ be a prime, and assume that the images of $N$ and of $q$ in $k$ are nonzero. Inside the field $\mathrm{LaurentSeries}(k)$ of formal Laurent series over $k$, consider the element `jqModC k`, namely $t^{-1}$ times the power series obtained from the integral series `jNum` by reducing its coefficients into $k$ (the $q$-expansion of $j$ with coefficients in $k$), and, for each $M \in \{N, q, Nq\}$, the element `jqNModC k M`, the image of `jqModC k` under the substitution operator `qExpand k M` (playing the role of $j(q^M)$). The field `charLDegeneracyRoof k N q` is the intermediate field of $\mathrm{LaurentSeries}(k)$ generated over $k$ by these four elements. The assertion is that this extension of $k$ has principal divisors in the project's sense: for every nonzero $f$ in it there is a finitely supported function $D$ from the set of places of the extension — valuation subrings containing the image of $k$, different from the whole field, and principal ideal rings — to $\mathbb{Z}$ such that $D(v) = \mathrm{ord}_v(f)$ at every place $v$, and such that the degree $\sum_v D(v)\deg(v)$ vanishes.
--
--   The field in question is the common home of the two degeneracy maps $X_0(Nq) \rightrightarrows X_0(N)$ realised through $q$-expansions in characteristic $\ell$, and the statement is the finiteness-plus-degree-zero property of divisors of functions on it, i.e. the statement that it behaves as the function field of a curve over $k$. It is supplied as the divisor-theoretic input for the characteristic-$\ell$ Hecke correspondence and specialisation constructions on modular curves, which invoke it for arbitrary level $N$ and auxiliary prime $q$ invertible in $k$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof.lean

import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve in

theorem ModularCurve.hasPrincipalDivisors_charLDegeneracyRoof (k : Type*)
    [Field k] (N q : ℕ) [NeZero N] [NeZero q] [Fact q.Prime]
    (hN : (N : k) ≠ 0) (hq : (q : k) ≠ 0) :
    HasPrincipalDivisors k (charLDegeneracyRoof k N q) := by sorry
