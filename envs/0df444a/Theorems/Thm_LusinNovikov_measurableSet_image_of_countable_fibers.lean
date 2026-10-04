-- Prove2me | Theorems.Thm_LusinNovikov_measurableSet_image_of_countable_fibers
-- name    : LusinNovikov.measurableSet_image_of_countable_fibers
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T10:20:32.915192+00:00
-- url     : https://prove2.me/theorems/13a8879c-ca2c-4549-9410-3e6192e39888
-- title:
--   A countable-to-one Borel map sends Borel sets to Borel sets
-- statement:
--   Let $f : X \to Y$ be a Borel map whose fibres $f^{-1}(y)$ are all countable, and let $A \subseteq X$ be Borel. Then the image $f(A)$ is a Borel subset of $Y$.
--
--   Here $X$ and $Y$ are standard Borel spaces (`StandardBorelSpace`), “Borel” means measurable for their σ-algebras, and $X \times Y$ carries the product σ-algebra. For injective $f$ this is the Lusin–Souslin theorem (in Mathlib, `MeasurableSet.image_of_measurable_injOn`); without the countability hypothesis the image is only analytic in general.
--
--   The proof covers $X$ by countably many Borel sets $S_n$ on each of which $f$ is injective (`LusinNovikov.exists_injOn_cover_of_countable_fibers`) and writes $f(A)$ as the union of the images $f(A \cap S_n)$, each Borel by the Lusin–Souslin theorem.
-- source:
--   A consequence of Kechris, A. S., Classical Descriptive Set Theory, Graduate Texts in Mathematics 156, Springer, 1995, https://doi.org/10.1007/978-1-4612-4190-4, p. 123, Theorem 18.10 (Lusin–Novikov), with the Lusin–Souslin theorem on injective Borel images; the proof follows Shinko, F., Lusin-Novikov via σ-ideals, unpublished note, 2024, formerly at https://math.berkeley.edu/~forte/notes/lusin_novikov.pdf, archived at https://web.archive.org/web/20250528233720/https://math.berkeley.edu/~forte/notes/lusin_novikov.pdf (no DOI)

import Mathlib

namespace LusinNovikov

theorem measurableSet_image_of_countable_fibers {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    {f : X → Y} (hf : Measurable f) (hfib : ∀ y, (f ⁻¹' {y}).Countable)
    {A : Set X} (hA : MeasurableSet A) : MeasurableSet (f '' A) := by
  sorry

end LusinNovikov
