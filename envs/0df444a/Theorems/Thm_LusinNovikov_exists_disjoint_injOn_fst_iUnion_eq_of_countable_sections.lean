-- Prove2me | Theorems.Thm_LusinNovikov_exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections
-- name    : LusinNovikov.exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T10:20:06.529345+00:00
-- url     : https://prove2.me/theorems/f518f2a6-83b0-4491-a902-e93d0911382b
-- title:
--   Lusin–Novikov — a Borel set with countable sections is a countable disjoint union of Borel graphs
-- statement:
--   Let $P \subseteq X \times Y$ be a Borel set whose every vertical section $P_x = \{y \mid (x, y) \in P\}$ is countable. Then $P$ is the union of a sequence $G_0, G_1, \dots$ of pairwise disjoint Borel sets, each of which is a graph: if $(x, y)$ and $(x, y')$ both lie in $G_n$, then $y = y'$ (the first projection is injective on $G_n$).
--
--   Here $X$ and $Y$ are standard Borel spaces (`StandardBorelSpace`), “Borel” means measurable for their σ-algebras, and $X \times Y$ carries the product σ-algebra. "Countable" includes finite.
--
--   Kechris states the Lusin–Novikov theorem as Theorem 18.10 (p. 123): for a Borel $P \subseteq X \times Y$ all of whose sections $P_x$ are countable, $P$ has a Borel uniformization, its projection is Borel, and $P$ is a countable union of Borel graphs. This is the last of the three claims, with the graphs in addition pairwise disjoint. The proof here does not follow Kechris: it is Shinko's argument with σ-ideals (2024), which proves that a continuous map of Polish spaces with countable fibres is injective on each of countably many Borel sets covering its domain (`LusinNovikov.exists_injOn_cover_of_countable_fibers`), and applies it to the projection $P \to X$.
-- source:
--   Kechris, A. S., Classical Descriptive Set Theory, Graduate Texts in Mathematics 156, Springer, 1995, https://doi.org/10.1007/978-1-4612-4190-4, p. 123, Theorem 18.10 (Lusin–Novikov), second sentence; the proof follows Shinko, F., Lusin-Novikov via σ-ideals, unpublished note, 2024, formerly at https://math.berkeley.edu/~forte/notes/lusin_novikov.pdf, archived at https://web.archive.org/web/20250528233720/https://math.berkeley.edu/~forte/notes/lusin_novikov.pdf (no DOI)

import Mathlib

namespace LusinNovikov

theorem exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    {P : Set (X × Y)} (hP : MeasurableSet P) (hcount : ∀ x, {y | (x, y) ∈ P}.Countable) :
    ∃ G : ℕ → Set (X × Y), (∀ n, MeasurableSet (G n)) ∧ (∀ n, Set.InjOn Prod.fst (G n)) ∧
      Pairwise (Function.onFun Disjoint G) ∧ ⋃ n, G n = P := by
  sorry

end LusinNovikov
