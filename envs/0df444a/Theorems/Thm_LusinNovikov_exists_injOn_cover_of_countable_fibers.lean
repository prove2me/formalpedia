-- Prove2me | Theorems.Thm_LusinNovikov_exists_injOn_cover_of_countable_fibers
-- name    : LusinNovikov.exists_injOn_cover_of_countable_fibers
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T10:20:20.212413+00:00
-- url     : https://prove2.me/theorems/56a36182-ad8e-45dd-8475-a3b0c721fc6a
-- title:
--   A countable-to-one Borel map is injective on each of countably many Borel sets covering its domain
-- statement:
--   Let $f : X \to Y$ be a Borel map whose fibres $f^{-1}(y)$ are all countable. Then there are Borel sets $S_0, S_1, \dots \subseteq X$ with $\bigcup_n S_n = X$ such that $f$ is injective on each $S_n$.
--
--   Here $X$ and $Y$ are standard Borel spaces (`StandardBorelSpace`), “Borel” means measurable for their σ-algebras, and $X \times Y$ carries the product σ-algebra.
--
--   Shinko (2024) proves, for a continuous map $f : X \to Y$ of Polish spaces, that exactly one of the following holds: $X$ can be covered by countably many Borel sets on each of which $f$ is injective, or some fibre of $f$ contains a Cantor set. When the fibres are countable the second alternative is impossible, which gives this statement for continuous maps of Polish spaces; a Borel map of standard Borel spaces becomes continuous for suitable Polish topologies with the same Borel sets, which gives it in general. The proof here formalizes that argument. It is also Kechris's Theorem 18.10 (p. 123) applied to the set of pairs $(f(x), x)$, whose sections are the fibres of $f$.
-- source:
--   Shinko, F., Lusin-Novikov via σ-ideals, unpublished note, 2024, formerly at https://math.berkeley.edu/~forte/notes/lusin_novikov.pdf, archived at https://web.archive.org/web/20250528233720/https://math.berkeley.edu/~forte/notes/lusin_novikov.pdf (no DOI), the Lusin–Novikov theorem there in the case of countable fibres, for Borel maps of standard Borel spaces; equivalently Kechris, A. S., Classical Descriptive Set Theory, Graduate Texts in Mathematics 156, Springer, 1995, https://doi.org/10.1007/978-1-4612-4190-4, p. 123, Theorem 18.10 applied to the set of pairs (f(x), x)

import Mathlib

namespace LusinNovikov

theorem exists_injOn_cover_of_countable_fibers {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    {f : X → Y} (hf : Measurable f) (hfib : ∀ y, (f ⁻¹' {y}).Countable) :
    ∃ S : ℕ → Set X, (∀ n, MeasurableSet (S n)) ∧ (∀ n, Set.InjOn f (S n)) ∧
      ⋃ n, S n = Set.univ := by
  sorry

end LusinNovikov
