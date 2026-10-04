-- Prove2me | Theorems.Thm_LodhaMoore_isXWord_or_eval_ne_of_sufficientlyExpanded
-- name    : LodhaMoore.isXWord_or_eval_ne_of_sufficientlyExpanded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T10:02:26.042429+00:00
-- url     : https://prove2.me/theorems/ebf95c5d-57ba-40cc-a61b-056fabe4cc0f
-- title:
--   Lemma 5.11 — a sufficiently expanded standard form is an X-word or does not evaluate to one
-- statement:
--   If $\Omega$ is a sufficiently expanded standard form, then either $\Omega$ is an $X$-word, or $\Omega$ evaluates to an element different from the value of every $X$-word.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 13, Lemma 5.11

import Mathlib
import Definitions.Def_LodhaMooreWords

namespace LodhaMoore

theorem isXWord_or_eval_ne_of_sufficientlyExpanded (Ω : Word) (hΩ : IsStandardForm Ω)
    (hse : SufficientlyExpanded Ω) : IsXWord Ω ∨ ∀ Ξ, IsXWord Ξ → Ω.eval ≠ Ξ.eval := by
  sorry

end LodhaMoore
