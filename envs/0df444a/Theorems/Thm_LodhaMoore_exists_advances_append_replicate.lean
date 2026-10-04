-- Prove2me | Theorems.Thm_LodhaMoore_exists_advances_append_replicate
-- name    : LodhaMoore.exists_advances_append_replicate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T09:51:09.034027+00:00
-- url     : https://prove2.me/theorems/2f548157-0731-4947-a0a8-76e63e692f1b
-- title:
--   Lemma 5.10 — a word without potential cancellations can be extended and advanced to s yⁿ
-- statement:
--   If a $B$-word $\Lambda$ has no potential cancellation, there are finite binary sequences $u$ and $s$ such that $\Lambda^\frown u$ can be advanced to $s^\frown y^n$, where $n$ is the number of occurrences of $y$ and $y^{-1}$ in $\Lambda$.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 13, Lemma 5.10

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_LodhaMooreWords

namespace LodhaMoore

theorem exists_advances_append_replicate (Λ : BWord) (h : NoPotentialCancellation Λ) :
    ∃ u s : Seq, Advances (Λ ++ u.map fun d => if d then BLetter.one else .zero)
      (s.map (fun d => if d then BLetter.one else .zero) ++
        List.replicate (Λ.countP fun l => l = .y ∨ l = .yinv) BLetter.y) := by
  sorry

end LodhaMoore
