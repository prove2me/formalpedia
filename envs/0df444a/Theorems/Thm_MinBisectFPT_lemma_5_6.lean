-- Prove2me | Theorems.Thm_MinBisectFPT_lemma_5_6
-- name    : MinBisectFPT.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:21.229164+00:00
-- url     : https://prove2.me/theorems/5f31127f-0437-4895-9e1d-a949497e7d0f
-- title:
--   Lemma 5.6 — $\mathrm{Decompose}(V(G))$ returns a decomposition with (D1)–(D3), for every run
-- statement:
--   Let $G$ be connected on $n$ vertices and $k\ge1$.
--
--   1. $V(G)$ is a legal input of $\mathrm{Decompose}$, and every legal input has a finished run.
--   2. Every finished run of $\mathrm{Decompose}(V(G))$, under all free choices, returns a rooted tree decomposition of $G$ with nonempty bags, at most $n$ nodes and properties (D1)–(D3); and each of its calls on a set $D$ creates a node $t$ with $\gamma(t)=D\cup N(D)$, $\sigma(t)=N(D)$ and $G_t=H_D$.
--   3. **Termination.** Along any finished run the set of a child call is a strict subset of the set of its parent; in a call, a loop runs for at most $|V(H)|$ iterations; and every partial execution of a loop can be continued until the loop ends.
--
--   **Formalization Note** A finished run is a finite object, so "terminates" is expressed by the clauses of item 3 and the existence in item 1, which together exclude stuck and infinite executions.
--
--   Differences from the source:
--   - reading: "terminates" → clauses: a run exists; child sets strictly shrink; at most $|V(H)|$ iterations of a loop (p.20); any partial loop continues to its end; reason: a run as a finite record cannot express nontermination, and these clauses exclude it
--   - generalization: $\mathrm{Decompose}(V(G))$ has a run → every legal input has a run; reason: $V(G)$ is legal by the first clause; the recursive calls need it
--   - encoding: the tree returned by recursion → a parent array with a set per node, numbered arbitrarily; reason: a recursion tree and its numbering carry the same data
--   - encoding: graphs $G_t$, $H_D$ on their own vertex sets → the same graphs on the ambient `Fin n`, with the other vertices isolated and every $X\subseteq V(H)$ written `X ⊆ VH`; reason: isolated ambient vertices change no cut and no neighbourhood
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 5.6, p.19; p.20

import Mathlib
import Definitions.Def_MinBisectFPT_IsDecomposeRun
import Definitions.Def_MinBisectFPT_IsUnbreakableTD

open scoped Classical

namespace MinBisectFPT

/-- **Lemma 5.6.** Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 5.6, p.19: "The call Decompose(V(G)) terminates and returns a rooted tree
decomposition of G with nonempty bags, at most n nodes, and properties (D1)–(D3). Each call Decompose(D)
creates a node t with γ(t) = D ∪ N(D), σ(t) = N(D), and G_t = H_D."

**Formalization Note** The third clause is over every run, under all free choices. A run is a finite object, so
termination is stated as five facts that exclude a stuck or an infinite execution: `V(G)` is a legal
call; every legal call has a run; along a run the sets of the calls strictly decrease; at most `|V(H)|`
iterations of the loop occur in a call (p.20); and any partial loop can be continued until it ends. -/
theorem lemma_5_6 {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) (k : ℕ) (hk : 1 ≤ k) :
    IsLegalCall G k Finset.univ ∧
    (∀ D₀, IsLegalCall G k D₀ → ∃ (T : RootedTD n) (call : Fin T.N → Finset (Fin n)),
      IsDecomposeRun G k D₀ T call) ∧
    (∀ (T : RootedTD n) (call : Fin T.N → Finset (Fin n)), IsDecomposeRun G k Finset.univ T call →
      IsRootedTD G T ∧ T.N ≤ n ∧ IsUnbreakableTD G T k ∧
        ∀ t, T.cone t = callVerts G (call t) ∧ T.adhesion t = nbr G (call t) ∧
          subtreeGraph G T t = callGraph G (call t)) ∧
    (∀ D₀ (T : RootedTD n) (call : Fin T.N → Finset (Fin n)), IsDecomposeRun G k D₀ T call →
      ∀ t c, T.parent c = some t → call c ⊂ call t) ∧
    ∀ D Z, IsCallSetup G k D Z →
      (∀ (m : ℕ) (β : ℕ → Finset (Fin n)), β 0 = callVerts G D →
        (∀ i < m, LoopStep (callGraph G D) (callVerts G D) Z k (β i) (β (i + 1))) →
          m ≤ (callVerts G D).card) ∧
      ∀ β, Relation.ReflTransGen (LoopStep (callGraph G D) (callVerts G D) Z k) (callVerts G D) β →
        ∃ β', Relation.ReflTransGen (LoopStep (callGraph G D) (callVerts G D) Z k) β β' ∧
          LoopEnded (callGraph G D) Z β' k := by sorry

end MinBisectFPT
