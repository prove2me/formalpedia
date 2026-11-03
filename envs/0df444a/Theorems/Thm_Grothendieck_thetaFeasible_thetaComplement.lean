-- Prove2me | Theorems.Thm_Grothendieck_thetaFeasible_thetaComplement
-- name    : Grothendieck.thetaFeasible_thetaComplement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T15:04:50.832622+00:00
-- url     : https://prove2.me/theorems/b5868365-a6dc-499c-b2ea-78bf41e44b0a
-- title:
--   The theta semidefinite program attains its infimum
-- statement:
--   Let $G=(V,E)$ be a finite graph with $V\neq\emptyset$ and let
--
--   $$\vartheta(G)=\inf\{\lambda\;:\;\exists Z\succeq0,\ Z_{uu}=\lambda-1\ (u\in V),\ Z_{uv}=-1\ (\{u,v\}\in E)\}.$$
--
--   Then the infimum is attained: there is a positive semidefinite $Z$ with diagonal $\vartheta(G)-1$ and off-diagonal entries $-1$ across the edges. The paper's semidefinite program (4.1) is written as a minimum, and the proof of Lemma 4.1 uses an *optimal* $Z$; this node justifies taking one.
--
--   The argument is compactness. The feasible $\lambda$ form a nonempty set bounded below by $1$ (the diagonal is nonnegative), so take a minimizing sequence $(\lambda_n)$ and feasible $Z_n$ with $\lambda_n\downarrow\vartheta(G)$. The diagonal entries are $\lambda_n-1$, bounded; positivity makes $|(Z_n)_{uv}|^2\le (Z_n)_{uu}(Z_n)_{vv}$, so every entry is bounded, and a subsequence converges. The constraints — positive semidefiniteness (closed) and the prescribed diagonal and off-diagonal entries — pass to the limit, giving a feasible $Z$ at $\lambda=\vartheta(G)$.
--
--   **Formalization Note** Exactly hypothesis `hZ` of the published reduction `Grothendieck.vector_construction_of_theta`, so Lemma 4.1 no longer has to assume an optimal solution.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — equation (4.1), p. 92; use of an optimal $Z$ in Lemma 4.1, p. 94.

import Mathlib
import Definitions.Def_Grothendieck_Theta

open scoped BigOperators Real

namespace Grothendieck

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The theta program attains its value.** For a nonempty vertex set there is a feasible `Z`
at `λ = ϑ(G)`, so the infimum defining `thetaComplement` is a minimum. -/
theorem thetaFeasible_thetaComplement (G : SimpleGraph V) [Nonempty V] :
    ThetaFeasible G (thetaComplement G) := by sorry

end Grothendieck
