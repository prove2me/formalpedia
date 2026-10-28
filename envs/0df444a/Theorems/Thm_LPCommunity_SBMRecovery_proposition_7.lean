-- Prove2me | Theorems.Thm_LPCommunity_SBMRecovery_proposition_7
-- name    : LPCommunity.SBMRecovery.proposition_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:03:21.848117+00:00
-- url     : https://prove2.me/theorems/51b89947-b49b-46ab-8596-ecf899c2fea6
-- title:
--   Proposition 7, p. 24 — Tutte's f-factor theorem
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and $f\in\mathbb Z_{\ge0}^V$. For disjoint $S,T\subseteq V$ let $\widetilde Q(S,T)$ be the number of connected components $C$ of $G-(S\cup T)$ with $f(C)+N(C,T)\equiv1\pmod 2$. Then $G$ has an $f$-factor if and only if, for all disjoint $S,T\subseteq V$,
--   $$
--   f(S)-f(T)+\sum_{v\in T}d(v)-N(S,T)-\widetilde Q(S,T)\ \ge\ 0 .
--   $$
--   Here $d(v)$ is the degree of $v$ in $G$, $f(U)=\sum_{v\in U}f(v)$, and $N(U,U')$ counts edges with one endpoint in $U$ and one in $U'$.
--
--   This is Tutte's $f$-factor theorem (1952). In the paper it is applied with $f\equiv d_{\mathrm{reg}}$ to show that a dense random graph contains a spanning regular subgraph (Proposition 4).
--
--   **Formalization Note** The left-hand side is computed in $\mathbb Z$. Mathlib's `SimpleGraph.tutte` is only the case $f\equiv1$ (perfect matchings).
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 24, Proposition 7 (Tutte [40])

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Factors

open Finset Filter Topology
open scoped Classical

namespace LPCommunity.SBMRecovery

/-- Proposition 7 (p. 24; Tutte's f-factor theorem): `G` has an `f`-factor iff for all disjoint
`S, T ⊆ V`, `f(S) − f(T) + ∑_{v ∈ T} d(v) − N(S, T) − Q̃(S, T) ≥ 0`. -/
theorem proposition_7 {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → ℕ) :
    HasFactor G f ↔
      ∀ S T : Finset V, Disjoint S T →
        0 ≤ (∑ v ∈ S, (f v : ℤ)) - (∑ v ∈ T, (f v : ℤ)) + (∑ v ∈ T, (G.degree v : ℤ))
          - (edgeCount G S T : ℤ) - (oddComps G f S T : ℤ) := by sorry

end LPCommunity.SBMRecovery
