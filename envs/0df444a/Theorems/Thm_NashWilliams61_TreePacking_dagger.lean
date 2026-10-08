-- Prove2me | Theorems.Thm_NashWilliams61_TreePacking_dagger
-- name    : NashWilliams61.TreePacking.dagger
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:28:07.921134+00:00
-- url     : https://prove2.me/theorems/07b63c26-b015-427d-8dba-08dc62696bce
-- title:
--   (†) — undoing a fusion in a spanning tree of $\Phi G$ through $\rho$
-- statement:
--   Let $G = (V, F)$ be a finite multigraph without loops and $\Phi$ a fusion at $\xi$, removing the edges $\lambda$ (joining $\xi, \eta$) and $\mu$ (joining $\xi, \zeta$) and inserting the new edge $\rho$ (joining $\eta, \zeta$). Let $H$ be a spanning tree of $\Phi G$ with $\rho \in E(H)$. Then:
--
--   1. if $\eta$ is in the same component of $H - \rho$ as $\xi$, then $\Phi^{-1}H - \lambda$ is a spanning tree of $G$;
--   2. if $\zeta$ is in the same component of $H - \rho$ as $\xi$, then $\Phi^{-1}H - \mu$ is a spanning tree of $G$.
--
--   Here $\Phi^{-1}H$ has edge set $(E(H) \setminus \{\rho\}) \cup \{\lambda, \mu\}$. This is the single step that Lemma 4 iterates.
--
--   **Formalization Note** $\Phi G$ keeps the vertex $\xi$, so a spanning tree of $\Phi G$ spans $V$, and $\Phi^{-1}H$ again has vertex set $V$; the paper's "is a tree" is therefore stated as "is a spanning tree of $G$". The paper's "according as" is stated as the two implications.
-- source:
--   Nash-Williams, Edge-disjoint spanning trees of finite graphs, J. London Math. Soc. 36 (1961), p. 447, claim (†)

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Definitions.Def_NashWilliams61_TreePacking_Fusions
open NagamochiIbaraki.EdgeConn

namespace NashWilliams61.TreePacking

/-- **(†)** (Nash-Williams 1961, p. 447). Let `Φ` be a fusion at `ξ` of `G = (V, F)`. If
`H` is a spanning tree of `ΦG` and `ρ ∈ E(H)`, then `Φ⁻¹H − λ` is a spanning tree of `G`
if `η` is in the same component of `H − ρ` as `ξ`, and `Φ⁻¹H − μ` is one if `ζ` is. -/
theorem dagger {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (F : Finset E) (φ : Fusion V E)
    (hφ : φ.IsValid ends F) (H : Finset E)
    (hH : IsSpanningTreeOn ends Finset.univ (φ.apply F) H) (hρ : φ.rho ∈ H) :
    ((edgeGraph ends (H.erase φ.rho)).Reachable φ.xi φ.eta →
        IsSpanningTreeOn ends Finset.univ F ((φ.inv (Finset.univ, H)).2.erase φ.lam)) ∧
      ((edgeGraph ends (H.erase φ.rho)).Reachable φ.xi φ.zeta →
        IsSpanningTreeOn ends Finset.univ F ((φ.inv (Finset.univ, H)).2.erase φ.mu)) := by sorry

end NashWilliams61.TreePacking
