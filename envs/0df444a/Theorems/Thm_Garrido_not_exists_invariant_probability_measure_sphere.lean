-- Prove2me | Theorems.Thm_Garrido_not_exists_invariant_probability_measure_sphere
-- name    : Garrido.not_exists_invariant_probability_measure_sphere
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-24T14:03:06.837728+00:00
-- url     : https://prove2.me/theorems/232162fc-7e6f-4b8c-a802-b72a0613051a
-- title:
--   p. 3 — no rotation-invariant finitely additive probability measure on Sⁿ, n ≥ 2
-- statement:
--   For $n \ge 2$ there is no finitely additive measure
--   $m : \mathcal{P}(S^n) \to [0,\infty]$, defined on every subset of the $n$-sphere, that is
--   invariant under $SO(n+1,\mathbb{R})$ and has $m(S^n) = 1$:
--
--   $$\nexists\, m : \mathcal{P}(S^n) \to [0,\infty] \ \text{finitely additive, rotation-invariant, with } m(S^n) = 1.$$
--
--   It is the measure-theoretic content of Corollary 1.9.
--
--   **Formalization Note.** Finite additivity and invariance are the imported
--   `IsFinitelyAdditiveMeasure` and `IsInvariant`; invariance is $m(A \cdot E) = m(E)$ for every
--   rotation $A$ and every $E \subseteq S^n$.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 3, the remark after Corollary 1.9; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_BanachTarski
import Definitions.Def_Garrido_Amenability
open scoped ENNReal

namespace Garrido

theorem not_exists_invariant_probability_measure_sphere (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∃ m : Set (Sphere n) → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧
      IsInvariant (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ) m ∧ m Set.univ = 1 := by
  sorry

end Garrido
