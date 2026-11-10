-- Prove2me | Theorems.Thm_FreeReplExchange_lemma_1
-- name    : FreeReplExchange.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:18:22.634498+00:00
-- url     : https://prove2.me/theorems/95e4cece-aa80-4815-a876-add06911a543
-- title:
--   Lemma 1 — tracked paths
-- statement:
--   Assume the sign conditions of §2.1 and fix a global tie order. Fix an agent $i\notin P$, and let $\mu_0$ and $\mu_1$ be the matchings selected by M3 in the initial exchange graphs $G(x^{(0)},P)$ and $G(x^{(0)},P\cup\{i\})$. Every connected component of $\mu_0\triangle\mu_1$ is a **tracked path**: a path whose consecutive edges alternate between $\mu_0$ and $\mu_1$, with at least one endpoint a slot $(i,s)$ of agent $i$.
--
--   This reduces the effect of $i$'s participation to utility changes along tracked paths, which is the core of the IR proof (Theorem 12).
--
--   Differences from the source:
--   - generalization: every good is initially held by at least one agent (WLOG, p.13) → any initial allocation x⁽⁰⁾; reason: no step of the proof uses the assumption; the source's instances are among those covered
--   - encoding: a total order e₁ ≺ ⋯ ≺ e_L on all potential exchanges, fixed independently of participation and history (p.32) → an injective rank rk on exchanges, smaller rank first, fixed before the participating set; reason: every total order on the finite type of exchanges arises from an injective rank, and only the order is used
--   - encoding: every connected component of μ0 △ μ1 → for every slot on an edge of the graph of μ0 △ μ1, a path containing every edge of that slot's component; reason: the components of an edge set are those spanned by its edges; a path containing all edges of a component is that component
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), p.35 (PDF p.37), Lemma 1

import Mathlib
import Definitions.Def_FreeReplExchange_m3Select

namespace FreeReplExchange

/-- Lemma 1 (Tracked paths), Yang–Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with
Negative Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…), p.35 (PDF p.37). Fix `i ∉ P`. Let `μ0` and `μ1` be the
matchings selected by M3 in the initial exchange graphs on `P` and `P ∪ {i}`. Every connected
component of `μ0 △ μ1` is a tracked path: an alternating path with at least one endpoint belonging
to agent `i`.

**Formalization Note.** `μ0 △ μ1` is the graph on slots whose edges are the slot edges of the
exchanges in exactly one of `μ0`, `μ1`; its components are those of its edges (every vertex
`v` lying on an edge). For such a `v` the statement gives a path `w` from `a` to `b` containing
every edge of the component of `v` (so the component is exactly the path), whose consecutive edges
alternate between `μ0` and `μ1`, with `a` or `b` a slot of agent `i`. The tie order is an
injective rank, fixed independently of the participating set. -/
theorem lemma_1 {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (hU : SignCond U)
    (rk : Exchange A m → ℕ) (hrk : Function.Injective rk) (P : Finset A) (i : A) (hi : i ∉ P) :
    let μ0 := m3Select U rk (edges x0 U P x0)
    let μ1 := m3Select U rk (edges x0 U (insert i P) x0)
    let G := slotGraph (symmDiff μ0 μ1)
    ∀ v : A × Fin m, (∃ e ∈ G.edgeSet, v ∈ e) →
      ∃ (a b : A × Fin m) (w : G.Walk a b), w.IsPath ∧
        (∀ e ∈ G.edgeSet, (∀ u ∈ e, G.Reachable v u) → e ∈ w.edges) ∧
        w.edges.Chain' (fun e e' =>
          (e ∈ (slotGraph μ0).edgeSet ∧ e' ∈ (slotGraph μ1).edgeSet) ∨
            (e ∈ (slotGraph μ1).edgeSet ∧ e' ∈ (slotGraph μ0).edgeSet)) ∧
        (a.1 = i ∨ b.1 = i) := by sorry

end FreeReplExchange
