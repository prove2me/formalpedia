-- Prove2me | Theorems.Thm_LodhaMoore_pow_ne_one_of_mem_G0_of_ne_one
-- name    : LodhaMoore.pow_ne_one_of_mem_G0_of_ne_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T20:16:30.481873+00:00
-- url     : https://prove2.me/theorems/96133d2e-aee5-461f-b0ee-caade7b4336d
-- title:
--   Abstract — G₀ is torsion-free
-- statement:
--   No element of $G_0$ other than the identity has finite order: if $g \in G_0$, $g \ne 1$ and $n > 0$, then $g^n \ne 1$.
--
--   **Formalization Note.** "The first such example" is a claim about the literature and is not formalized.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 1, Abstract

import Mathlib
import Definitions.Def_LodhaMoore

namespace LodhaMoore

theorem pow_ne_one_of_mem_G0_of_ne_one : ∀ g ∈ G0, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1 := by
  sorry

end LodhaMoore
