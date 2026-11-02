-- Prove2me | Theorems.Thm_Grothendieck_theta_ge_two
-- name    : Grothendieck.theta_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T04:18:01.293324+00:00
-- url     : https://prove2.me/theorems/25263b63-171a-40ac-93d5-87f5ef156a1a
-- title:
--   Proposition 4.2 (proof) — $\vartheta(G)\ge2$ for a graph with an edge
-- statement:
--   Let $G=(V,E)$ be a finite graph with at least one edge. Then the theta number of its complement satisfies
--
--   $$
--   \vartheta(G)\ \ge\ 2 .
--   $$
--
--   The paper uses this fact in the proof of Proposition 4.2 to conclude that the right-hand side $1/(\vartheta(G)-1)$ of the defining equation of $\beta(r,G)$ is a finite number, and that the relevant series has to be evaluated at a number $\beta\le1$.
--
--   The lower bound follows directly from the semidefinite program. If $Z\succeq0$ has $Z(u,u)=\lambda-1$ for every vertex and $Z(u,v)=-1$ across an edge, then $\lambda-1=Z(u,u)\ge0$; and applying positive semidefiniteness to the two-dimensional subspace spanned by the coordinate vectors of the endpoints of the edge gives $Z(u,v)^2\le Z(u,u)Z(v,v)$, i.e. $1\le(\lambda-1)^2$, hence $\lambda-1\ge1$. The converse bound $\vartheta(G)\le|V|$ — that the program is feasible at all — is supplied by the regular simplex: the $|V|\times|V|$ matrix $|V|\cdot I-J$ is positive semidefinite with diagonal $|V|-1$ and off-diagonal entries $-1$, so $\lambda=|V|$ is feasible.
--
--   **Formalization Note** Stated for `thetaComplement G`, the `sInf` of the feasible set of equation (4.1). Both halves of the argument — the positivity/normality bound and the feasibility of $\lambda=|V|$ — are parts of the proof of this statement.
-- source:
--   J. Briët, F. M. de Oliveira Filho, F. Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105, proof of Proposition 4.2, p. 93 ("Since $G$ has at least one edge, we have $\vartheta(G)\ge2$"), and p. 92 for the regular-simplex feasible solution of (4.1). https://doi.org/10.4086/toc.2014.v010a004

import Mathlib
import Definitions.Def_Grothendieck_Theta

namespace Grothendieck

theorem theta_ge_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hne : ∃ u v, G.Adj u v) : 2 ≤ thetaComplement G := by sorry

end Grothendieck
