-- Prove2me | Theorems.Thm_LodhaMoore_exists_mem_F_finAct_of_lexLt
-- name    : LodhaMoore.exists_mem_F_finAct_of_lexLt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T07:52:58.918567+00:00
-- url     : https://prove2.me/theorems/db2126a8-acab-4b05-acb8-b11d0042ff65
-- title:
--   Proposition 3.5 — an incompatible pair u <lex v is the image under F of a pair of length at most 3
-- statement:
--   If $u$ and $v$ are incompatible finite binary sequences with $u <_{\mathrm{lex}} v$, there are $g \in F$ and $s <_{\mathrm{lex}} t$ of length at most 3 with $s.g = u$ and $t.g = v$.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 6, Proposition 3.5

import Mathlib
import Definitions.Def_LodhaMoore

namespace LodhaMoore

theorem exists_mem_F_finAct_of_lexLt (u v : Seq) (huv : Incompatible u v) (hlt : LexLt u v) :
    ∃ g ∈ F, ∃ s t : Seq, LexLt s t ∧ s.length ≤ 3 ∧ t.length ≤ 3 ∧ FinAct g s u ∧ FinAct g t v := by
  sorry

end LodhaMoore
