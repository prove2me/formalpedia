-- Prove2me | Theorems.Thm_NondetConn_Supplement_theorem_6_2
-- name    : NondetConn.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:12:20.760426+00:00
-- url     : https://prove2.me/theorems/5ccf169e-de15-4535-9ad1-2d835227d079
-- title:
--   Theorem 6.2 — round-dependent lower bounds for five graph properties
-- statement:
--   For every fixed error probability $\varepsilon\in(0,1/2)$, there is $c>0$ with the following property. For every positive $r:\mathbb N\to\mathbb N$ satisfying $r(N)=o(\log_2 N)$ there is $N_0$ such that every $N\ge N_0$ has the following five properties. Any Alice-first randomized protocol using at most $r(N)$ rounds and error at most $\varepsilon$ communicates at least
--   $$
--   c\frac{N}{r(N)}\log_2N
--   $$
--   bits to decide whether an $N$-vertex graph is (1) bipartite, (2) cycle-free, (3) Eulerian, (4) Hamiltonian, or (5) planar.
--
--   Each input graph is split into disjoint edge sets held by Alice and Bob.
--
--   Differences from the source:
--   - reading: $r=o(\log N)$ and a lower bound $\Omega((N/r)\log N)$ for each of five properties → for each fixed error, one common positive constant for all five clauses and every positive round family with quotient tending to zero, followed by a family-dependent threshold; reason: finitely many source omega constants can be replaced by their positive minimum, and no constant depends on the growing $N$ or $r(N)$
--   - encoding: an $N$-vertex graph whose edges are split between the parties → two disjoint Mathlib simple graphs on `Fin N`, with each property evaluated on their union; reason: this is the paper's undirected edge-partition input model
--   - encoding: planar graph → the published predicate asserting a crossing-free plane drawing by simple arcs; reason: this is standard graph planarity and adds no graph restriction
--   - encoding: an $r$-round randomized protocol with receiver-only output → a finite communication tree with at most $r(N)$ alternating sender blocks, receiver-only correctness, and both outputs checked only when no message is sent; reason: this represents the same interactive protocols and resolves the source's undefined zero-message receiver without affecting the eventual lower bound
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Theorem 6.2, p.21 (PDF p.23)

import Definitions.Def_NondetConn_Supplement_communicationRounds
import Definitions.Def_NondetConn_Supplement_decidesGraphProperty
import Definitions.Def_NondetConn_Supplement_solves
import Definitions.Def_NondetConn_Supplement_startsWith

set_option autoImplicit false

namespace NondetConn.Supplement

open Filter CommThresholdPR.StrongConverse

/-- **Theorem 6.2** (Zhang, *Settling Nondeterministic Communication Complexity of Graph
Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), printed p.21,
PDF p.23). For `r(N)=o(log₂ N)`, deciding any of bipartiteness, cycle-freeness,
Eulerianity, Hamiltonicity, or planarity of an `N`-vertex split-edge graph with fixed error
below `1/2` requires `Ω((N/r(N)) log₂ N)` randomized communication.

**Formalization Note** Each input is a pair of disjoint Mathlib simple graphs on `Fin N`; the
property is tested on their union. Planarity is the published crossing-free plane-drawing
predicate. The five conjuncts retain all five clauses of the printed theorem. -/
theorem theorem_6_2 :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ c : ℝ, 0 < c ∧ ∀ rounds : ℕ → ℕ,
      Tendsto (fun N ↦ (rounds N : ℝ) / Real.logb 2 N) atTop (nhds 0) →
      (∀ N, 1 ≤ rounds N) →
      ∃ N₀ : ℕ, ∀ N, 1 ≤ N → N₀ ≤ N →
        let lower := c * ((N : ℝ) / (rounds N : ℝ)) * Real.logb 2 N
        let good (property : GraphProperty)
            (P : Protocol (SimpleGraph (Fin N)) (SimpleGraph (Fin N)) Bool Bool) : Prop :=
          startsWith P true →
          (∀ GA GB ω z, P.publicLaw ω ≠ 0 → (P.tree ω).finiteRun GA GB z ≠ 0 →
            communicationRounds (P.tree ω) (P.bits ⟨ω, z.1⟩) ≤ rounds N) →
          solves P Disjoint (decidesGraphProperty property N) ε → lower ≤ (P.cost : ℝ)
        (∀ P, good .bipartite P) ∧
        (∀ P, good .cycleFree P) ∧
        (∀ P, good .eulerian P) ∧
        (∀ P, good .hamiltonian P) ∧
        (∀ P, good .planar P) := by sorry

end NondetConn.Supplement
