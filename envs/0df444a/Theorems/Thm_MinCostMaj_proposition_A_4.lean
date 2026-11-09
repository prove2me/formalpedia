-- Prove2me | Theorems.Thm_MinCostMaj_proposition_A_4
-- name    : MinCostMaj.proposition_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:19:53.000146+00:00
-- url     : https://prove2.me/theorems/4deee4d5-7d35-4e74-95e1-99c720a39423
-- title:
--   Proposition A.4 — a proper 2-absorbing subset gives a proper arc-consistent subinstance
-- statement:
--   Let $I$ be a finite arc-consistent instance (opposite readings) with a conservative commutative binary polymorphism $\{f_x\}_x$. If there are a variable $x$ and a set $B\subsetneq A_x$ that 2-absorbs $A_x$, then $I$ has a proper arc-consistent subinstance: an arc-consistent $I'\le I$ with $A^{I'}_u\subsetneq A^I_u$ for some $u$.
--
--   With Proposition A.3 this reduces the linked case of Theorem A.1 to Item 1.
--
--   Differences from the source:
--   - reading: instances of CSP(A) on a variable set V → finite variable and value types (`Finite V`, `Finite D`) with the opposite-readings convention `IsSymm` as a hypothesis; reason: instances are finite inputs and §3 assumes R_vu holds the opposite readings of R_uv for every instance
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Proposition A.4, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_MinCostMaj_BinInst
import Definitions.Def_MinCostMaj_Pattern
import Definitions.Def_MinCostMaj_BinPol

namespace MinCostMaj

/-- **Proposition A.4**, p.13 (PDF p.14; proof pp.17–18).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Proposition A.4, p.13: "Let I be a binary arc-consistent instance with a conservative
commutative binary polymorphism {fx}x. If there are x and B ⊊ Ax such that B 2-absorbs Ax, then I
has a proper arc-consistent subinstance."

A proper arc-consistent subinstance is an arc-consistent `I′ ≤ I` with some `A^{I′}_u ⊊ A^I_u`.

**Formalization Note.** Finite instance with §3's opposite-readings convention; arc-consistent
instances are binary in the sense of Appendix A. -/
theorem proposition_A_4 {V D : Type*} [Finite V] [Finite D] (I : BinInst V D) (hS : I.IsSymm)
    (hAC : I.IsArcConsistent) (f : V → D → D → D) (hf : I.IsConsCommBinPol f) (x : V)
    (B : Set D) (hBx : B ⊂ I.pot x) (hB : I.TwoAbsorbs f x B) :
    I.HasProperACSub := by sorry

end MinCostMaj
