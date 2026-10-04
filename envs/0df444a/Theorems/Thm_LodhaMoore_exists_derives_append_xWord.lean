-- Prove2me | Theorems.Thm_LodhaMoore_exists_derives_append_xWord
-- name    : LodhaMoore.exists_derives_append_xWord
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T08:57:37.659998+00:00
-- url     : https://prove2.me/theorems/7926c8f9-6343-4c04-8edf-d7ac2c44c355
-- title:
--   Lemma 5.3 — appending an X-word to a deep standard form lowers the depth by at most its length
-- statement:
--   For every $X$-word $\Xi$ there is $l_0$ such that for every standard form $\Omega$ of depth at least $l_0$ (possibly infinite), some standard form $\Omega'$ can be derived from $\Omega\Xi$ whose depth is at least the depth of $\Omega$ minus the word length of $\Xi$.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 10, Lemma 5.3

import Mathlib
import Definitions.Def_LodhaMooreWords

namespace LodhaMoore

theorem exists_derives_append_xWord (Ξ : Word) (hΞ : IsXWord Ξ) :
    ∃ l₀ : ℕ, ∀ Ω, IsStandardForm Ω → (l₀ : ℕ∞) ≤ depth Ω →
      ∃ Ω', Derives (Ω ++ Ξ) Ω' ∧ IsStandardForm Ω' ∧ depth Ω - Ξ.wordLength ≤ depth Ω' := by
  sorry

end LodhaMoore
