-- Prove2me | Theorems.Thm_LusinNovikov_exists_measurable_uniformization_of_countable_sections
-- name    : LusinNovikov.exists_measurable_uniformization_of_countable_sections
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T10:20:40.391099+00:00
-- url     : https://prove2.me/theorems/f6a30651-c640-4e0f-97a9-ad5cefcabe42
-- title:
--   Lusin–Novikov — a Borel set with countable sections has a Borel uniformization
-- statement:
--   Let $P \subseteq X \times Y$ be a Borel set whose every vertical section $P_x = \{y \mid (x, y) \in P\}$ is countable, and let $Y$ be nonempty. Then there is a Borel function $g : X \to Y$ with $(x, g(x)) \in P$ for every $x$ in the projection of $P$, that is, for every $x$ with $P_x \neq \varnothing$.
--
--   Here $X$ and $Y$ are standard Borel spaces (`StandardBorelSpace`), “Borel” means measurable for their σ-algebras, and $X \times Y$ carries the product σ-algebra. The function is defined on all of $X$; off the projection of $P$ (a Borel set, by `LusinNovikov.measurableSet_image_fst_of_countable_sections`) its values are arbitrary. A uniformization in Kechris's sense, a function on the projection whose graph lies in $P$, is its restriction.
--
--   This is the first claim of the Lusin–Novikov theorem as Kechris states it (Theorem 18.10, p. 123). The proof covers $P$ by the graphs of countably many Borel functions $g_n$ on Borel sets $D_n$ and lets $g(x) = g_n(x)$ for the least $n$ with $x \in D_n$.
-- source:
--   Kechris, A. S., Classical Descriptive Set Theory, Graduate Texts in Mathematics 156, Springer, 1995, https://doi.org/10.1007/978-1-4612-4190-4, p. 123, Theorem 18.10 (Lusin–Novikov), first sentence; the proof follows Shinko, F., Lusin-Novikov via σ-ideals, unpublished note, 2024, formerly at https://math.berkeley.edu/~forte/notes/lusin_novikov.pdf, archived at https://web.archive.org/web/20250528233720/https://math.berkeley.edu/~forte/notes/lusin_novikov.pdf (no DOI)

import Mathlib

namespace LusinNovikov

theorem exists_measurable_uniformization_of_countable_sections {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    {P : Set (X × Y)} (hP : MeasurableSet P) (hcount : ∀ x, {y | (x, y) ∈ P}.Countable) :
    ∃ g : X → Y, Measurable g ∧ ∀ x ∈ Prod.fst '' P, (x, g x) ∈ P := by
  sorry

end LusinNovikov
