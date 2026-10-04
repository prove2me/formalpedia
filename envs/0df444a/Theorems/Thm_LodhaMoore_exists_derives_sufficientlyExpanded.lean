-- Prove2me | Theorems.Thm_LodhaMoore_exists_derives_sufficientlyExpanded
-- name    : LodhaMoore.exists_derives_sufficientlyExpanded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T09:24:48.89937+00:00
-- url     : https://prove2.me/theorems/7bb62a79-9d23-454d-a3c3-6ac2816c6be7
-- title:
--   Lemma 5.6 — every standard form derives a sufficiently expanded one
-- statement:
--   From every standard form some sufficiently expanded standard form can be derived.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 11, Lemma 5.6

import Mathlib
import Definitions.Def_LodhaMooreWords

namespace LodhaMoore

theorem exists_derives_sufficientlyExpanded (Ω : Word) (hΩ : IsStandardForm Ω) :
    ∃ Ω', Derives Ω Ω' ∧ IsStandardForm Ω' ∧ SufficientlyExpanded Ω' := by
  sorry

end LodhaMoore
