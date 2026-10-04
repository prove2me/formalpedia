-- Prove2me | Theorems.Thm_LodhaMoore_exists_derives_standardForm_le_depth
-- name    : LodhaMoore.exists_derives_standardForm_le_depth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T09:12:35.107395+00:00
-- url     : https://prove2.me/theorems/db085f78-12e8-40df-9dc8-432b6b3423a4
-- title:
--   Lemma 5.4 — every word derives a standard form of arbitrarily large depth
-- statement:
--   For every word $\Omega$ (nonzero exponents) and every $l \in \mathbb N$, some standard form of depth at least $l$ can be derived from $\Omega$.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 10, Lemma 5.4

import Mathlib
import Definitions.Def_LodhaMooreWords

namespace LodhaMoore

theorem exists_derives_standardForm_le_depth (Ω : Word) (hΩ : IsWord Ω) (l : ℕ) :
    ∃ Ω', Derives Ω Ω' ∧ IsStandardForm Ω' ∧ (l : ℕ∞) ≤ depth Ω' := by
  sorry

end LodhaMoore
