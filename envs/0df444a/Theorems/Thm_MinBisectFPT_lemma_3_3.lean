-- Prove2me | Theorems.Thm_MinBisectFPT_lemma_3_3
-- name    : MinBisectFPT.lemma_3_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T15:52:42.463347+00:00
-- url     : https://prove2.me/theorems/2eb524a6-a405-4ea8-a95a-caaefccc3bea
-- title:
--   Lemma 3.3 — Möbius inversion on the subset lattice
-- statement:
--   Let $\beta$ be a finite set, $R$ an abelian group, and $g,h:2^\beta\to R$. Then $g(W)=\sum_{U\subseteq W}h(U)$ holds for every $W\subseteq\beta$ if and only if
--   $$h(U)=\sum_{W\subseteq U}(-1)^{|U\setminus W|}g(W)$$
--   holds for every $U\subseteq\beta$.
--
--   Differences from the source:
--   - generalization: $R$ a truncated polynomial ring → any abelian group; reason: a truncated polynomial ring is an abelian group under addition
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 3.3, p.10

import Mathlib

open scoped Classical

namespace MinBisectFPT

/-- **Lemma 3.3 (Möbius inversion).** Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 3.3, p.10.

**Formalization Note** `R` is any abelian group, of which a truncated polynomial ring is an instance. -/
theorem lemma_3_3 {β R : Type} [Fintype β] [DecidableEq β] [AddCommGroup R]
    (g h : Finset β → R) :
    (∀ W, g W = ∑ U ∈ W.powerset, h U) ↔
      ∀ U, h U = ∑ W ∈ U.powerset, ((-1 : ℤ) ^ (U \ W).card) • g W := by sorry

end MinBisectFPT
