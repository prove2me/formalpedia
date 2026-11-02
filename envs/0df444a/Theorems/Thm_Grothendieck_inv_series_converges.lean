-- Prove2me | Theorems.Thm_Grothendieck_inv_series_converges
-- name    : Grothendieck.inv_series_converges
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-02T04:19:07.526834+00:00
-- url     : https://prove2.me/theorems/72109dab-6fd3-40a1-ad71-84b1c5caf36f
-- title:
--   Proposition 4.2 — the series converges to $E_r^{-1}$ at $t\beta(r,G)$
-- statement:
--   Let $r\ge1$ and let $G=(V,E)$ be a graph with at least one edge. Then $\beta(r,G)$ exists, and for every $t\in[-1,1]$ the series
--
--   $$
--   \sum_{k\ge0}b_{2k+1}\big(t\,\beta(r,G)\big)^{2k+1}
--   $$
--
--   converges to
--
--   $$
--   E_r^{-1}\big(t\,\beta(r,G)\big).
--   $$
--
--   In particular the series *with absolute values* converges at $t\beta(r,G)$, and the expansion of $E_r^{-1}$ is valid on the whole interval on which the rounding argument evaluates it. The proof distinguishes two cases. If the absolute-value series diverges at $c_r$, then continuity and strict increase on $[0,c_r)$ produce a solution $\beta<c_r$ of the defining equation, inside the convergence disc. If it converges at $c_r$, then the Taylor series of $E_r^{-1}$ converges absolutely and uniformly on the closed disc of radius $c_r$ and defines a continuous function there which agrees with $E_r^{-1}$; evaluating at $z=ic_r$ and using $E_r(i)=\pm ic_r$ gives $1\le f(c_r)$, whence $\beta\le c_r$. In both cases the series converges with the coefficients' absolute values, so the estimate carries over to the signed series for $|t|\le1$.
--
--   **Formalization Note** The statement has two conjuncts: summability of `fun k => invCoeff r (2*k+1) * (t * beta r G) ^ (2*k+1)`, and the identification of its sum with `ErInv r (t * beta r G)`, the inverse function of the definition layer.
-- source:
--   J. Briët, F. M. de Oliveira Filho, F. Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105, Proposition 4.2, p. 92, and its proof, pp. 93. https://doi.org/10.4086/toc.2014.v010a004

import Mathlib
import Definitions.Def_Grothendieck_Beta

namespace Grothendieck

theorem inv_series_converges {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (hr : 1 ≤ r) (G : SimpleGraph V) (hne : ∃ u v, G.Adj u v)
    (t : ℝ) (ht : |t| ≤ 1) :
    Summable (fun k : ℕ => invCoeff r (2 * k + 1) * (t * beta r G) ^ (2 * k + 1)) ∧
      (∑' k : ℕ, invCoeff r (2 * k + 1) * (t * beta r G) ^ (2 * k + 1)) =
        ErInv r (t * beta r G) := by sorry

end Grothendieck
