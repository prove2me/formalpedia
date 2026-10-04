-- Prove2me | Theorems.Thm_LusinNovikov_measurableSet_image_fst_of_countable_sections
-- name    : LusinNovikov.measurableSet_image_fst_of_countable_sections
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T10:20:38.748815+00:00
-- url     : https://prove2.me/theorems/1cb69ccf-6e49-4f24-af5e-33e190c1de81
-- title:
--   Lusin–Novikov — the projection of a Borel set with countable sections is Borel
-- statement:
--   Let $P \subseteq X \times Y$ be a Borel set whose every vertical section $P_x = \{y \mid (x, y) \in P\}$ is countable. Then its projection $\{x \in X \mid \exists y,\ (x, y) \in P\}$ is a Borel subset of $X$.
--
--   Here $X$ and $Y$ are standard Borel spaces (`StandardBorelSpace`), “Borel” means measurable for their σ-algebras, and $X \times Y$ carries the product σ-algebra. Without the countability hypothesis the projection is only analytic in general.
--
--   This is part of the Lusin–Novikov theorem as Kechris states it (Theorem 18.10, p. 123). The proof writes $P$ as a countable union of Borel graphs (`LusinNovikov.exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections`) and takes the image of each under the first projection, which is injective on it, so the image is Borel by the Lusin–Souslin theorem.
-- source:
--   Kechris, A. S., Classical Descriptive Set Theory, Graduate Texts in Mathematics 156, Springer, 1995, https://doi.org/10.1007/978-1-4612-4190-4, p. 123, Theorem 18.10 (Lusin–Novikov), first sentence; the proof follows Shinko, F., Lusin-Novikov via σ-ideals, unpublished note, 2024, formerly at https://math.berkeley.edu/~forte/notes/lusin_novikov.pdf, archived at https://web.archive.org/web/20250528233720/https://math.berkeley.edu/~forte/notes/lusin_novikov.pdf (no DOI)

import Mathlib

namespace LusinNovikov

theorem measurableSet_image_fst_of_countable_sections {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    {P : Set (X × Y)} (hP : MeasurableSet P) (hcount : ∀ x, {y | (x, y) ∈ P}.Countable) :
    MeasurableSet (Prod.fst '' P) := by
  sorry

end LusinNovikov
