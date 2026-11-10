-- Prove2me | Theorems.Thm_FreeReplExchange_lemma_3
-- name    : FreeReplExchange.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:16:51.059395+00:00
-- url     : https://prove2.me/theorems/b6e068b0-7e03-4389-af2e-6c5adb42043f
-- title:
--   Lemma 3 — first two objectives for bipartite matching
-- statement:
--   Let $H=(L,R,E)$ be a bipartite graph with finitely many edges, give each right vertex $v\in R$ a value $a_v>0$, and give every edge incident to $v$ that value; the value of a matching $K$ is $\sum_{(l,v)\in K}a_v$. If a matching $D$ has maximum cardinality and, among maximum-cardinality matchings, maximum total value, then
--   $$\sum_{(l,v)\in K}a_v\le\sum_{(l,v)\in D}a_v\qquad\text{for every matching }K\text{ of }H .$$
--
--   In the NIC proof it shows that optimizing the first two objectives of M3 already gives an agent her best set of exchanges under ESC.
--
--   Differences from the source: none.
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), p.37 (PDF p.39), Lemma 3

import Mathlib

namespace FreeReplExchange

/-- Lemma 3 (First two objectives for bipartite matching), Yang–Kandasamy, *Pairwise Exchanges of
Freely Replicable Goods with Negative Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…), p.37 (PDF p.39). Let
`H = (L, R, E)` be bipartite, give each `v ∈ R` a value `a_v > 0`, and give every edge incident to
`v` that value. A matching that has maximum cardinality and, among such matchings, maximum total
value also maximizes total value over all matchings of `H`.

**Formalization Note.** The sides are types `L`, `R`; the edge set is a finite `E ⊆ L × R`; a
matching is a subset of `E` injective on both coordinates; the value of a matching `K` is
`Σ_{(l, v) ∈ K} a_v`. -/
theorem lemma_3 {L R : Type*} [DecidableEq L] [DecidableEq R] (E : Finset (L × R)) (a : R → ℝ)
    (ha : ∀ v, 0 < a v) (D : Finset (L × R))
    (hD : D ⊆ E ∧ Set.InjOn Prod.fst (D : Set (L × R)) ∧ Set.InjOn Prod.snd (D : Set (L × R)))
    (hcard : ∀ K : Finset (L × R),
      K ⊆ E → Set.InjOn Prod.fst (K : Set (L × R)) → Set.InjOn Prod.snd (K : Set (L × R)) →
        K.card ≤ D.card)
    (hval : ∀ K : Finset (L × R),
      K ⊆ E → Set.InjOn Prod.fst (K : Set (L × R)) → Set.InjOn Prod.snd (K : Set (L × R)) →
        K.card = D.card → ∑ e ∈ K, a e.2 ≤ ∑ e ∈ D, a e.2) :
    ∀ K : Finset (L × R),
      K ⊆ E → Set.InjOn Prod.fst (K : Set (L × R)) → Set.InjOn Prod.snd (K : Set (L × R)) →
        ∑ e ∈ K, a e.2 ≤ ∑ e ∈ D, a e.2 := by sorry

end FreeReplExchange
