-- Prove2me | Theorems.Thm_MoritaEquiv_example4_morita
-- name    : MoritaEquiv.example4_morita
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T12:59:58.256686+00:00
-- url     : https://prove2.me/theorems/112a351f-fe4a-401f-a4b1-8b1da1c634d8
-- title:
--   Two kinds of things: one sort with p, q vs two sorts
-- statement:
--   The one-sorted theory $\{\exists x\,p(x),\ \exists x\,q(x),\ \forall x\,(p(x)\vee q(x)),\ \forall x\,\neg(p(x)\wedge q(x))\}$ is Morita equivalent to the empty theory in the signature with two sorts and no symbols.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (numbering as in arXiv v1), §3, Example 1 and §4.3, Example 4

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Barrett–Halvorson, Examples 1 and 4: "there are two kinds of things", said with two
predicates `p, q` partitioning one sort (`Ex1.T1`) or with two sorts and no axioms (`Ex1.T2`).
The theories are not definitionally equivalent (different sorts) but are Morita equivalent. -/
theorem example4_morita : MoritaEquivalent Ex1.T1 Ex1.T2 := by sorry

end MoritaEquiv
