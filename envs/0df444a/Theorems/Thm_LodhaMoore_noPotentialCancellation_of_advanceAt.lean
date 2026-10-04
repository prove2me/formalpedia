-- Prove2me | Theorems.Thm_LodhaMoore_noPotentialCancellation_of_advanceAt
-- name    : LodhaMoore.noPotentialCancellation_of_advanceAt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T09:38:46.620605+00:00
-- url     : https://prove2.me/theorems/7558499b-a21a-48af-91c6-5de7caefcb2a
-- title:
--   Lemma 5.9 — advancing preserves the absence of potential cancellations
-- statement:
--   If a $B$-word has no potential cancellation, then advancing any occurrence of $y^{\pm1}$ in it gives a $B$-word with no potential cancellation.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 12, Lemma 5.9

import Mathlib
import Definitions.Def_LodhaMooreWords

namespace LodhaMoore

theorem noPotentialCancellation_of_advanceAt (Λ Λ' : BWord) (i j : ℕ)
    (h : NoPotentialCancellation Λ) (hadv : AdvanceAt (Λ, i) (Λ', j)) : NoPotentialCancellation Λ' := by
  sorry

end LodhaMoore
