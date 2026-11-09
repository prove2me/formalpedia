-- Prove2me | Theorems.Thm_MinCostMaj_proposition_A_3
-- name    : MinCostMaj.proposition_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:19:40.180263+00:00
-- url     : https://prove2.me/theorems/e1fda032-6a6a-479e-81f1-2d52694c777d
-- title:
--   Proposition A.3 — a proper linked pattern relation gives a proper 2-absorbing subset
-- statement:
--   Let $I$ be a finite binary instance (constraints between the potatoes, opposite readings) with a conservative commutative binary polymorphism $\{f_x\}_x$. Let $p$ be a pattern from $x$ to $y$ and let
--   $$\mathrm{Conn}(p)=\{(a,b)\in A_x\times A_y : p\text{ connects }a\text{ to }b\}.$$
--   If $\mathrm{Conn}(p)$ is a proper linked relation in $A_x\times A_y$, then $A_x$ or $A_y$ has a proper 2-absorbing subset, i.e. a 2-absorbing $B\ne A_x$ (respectively $B\ne A_y$).
--
--   Together with Proposition A.4 this turns Item 3 of Theorem A.1 into Item 1.
--
--   Differences from the source:
--   - reading: binary instance → every constraint lies in A_x × A_y (`IsBinary`), finite variables and values, opposite readings (`IsSymm`); reason: f_x : A_x² → A_x must apply to the pairs of the constraints; instances are finite and follow §3's convention
--   - encoding: a pattern R_1,…,R_n along u = w_0,…,w_n = v → the start u and the list of steps (R_i, w_i); concatenation is list append; reason: same patterns
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Proposition A.3, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_MinCostMaj_BinInst
import Definitions.Def_MinCostMaj_Pattern
import Definitions.Def_MinCostMaj_BinPol

namespace MinCostMaj

/-- **Proposition A.3**, p.13 (PDF p.14; proof pp.16–17).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Proposition A.3, p.13: "Let I be a binary instance with a conservative commutative binary
polymorphism {fx}x. If some pattern defines a proper linked subrelation of A^I_x × A^I_y, then either
A^I_x or A^I_y has a proper 2-absorbing subset."

The relation defined by the pattern `l` from `x` to `y` on `A^I_x × A^I_y` is `patRel I x y l`.
A proper 2-absorbing subset is a 2-absorbing `B` (nonempty by Definition A.2) with `B ≠ A_x`.

**Formalization Note.** Finite instance, constraints between potatoes (`IsBinary`), §3's
opposite-readings convention (`IsSymm`); arc consistency is not assumed. -/
theorem proposition_A_3 {V D : Type*} [Finite V] [Finite D] (I : BinInst V D) (hS : I.IsSymm)
    (hB : I.IsBinary) (f : V → D → D → D) (hf : I.IsConsCommBinPol f) (x y : V)
    (l : List (Set (D × D) × V)) (hl : IsPat I.rels x l y)
    (hprop : IsProperRel (I.pot x) (I.pot y) (patRel I x y l))
    (hlink : IsLinked (I.pot x) (I.pot y) (patRel I x y l)) :
    (∃ B, I.TwoAbsorbs f x B ∧ B ≠ I.pot x) ∨ (∃ B, I.TwoAbsorbs f y B ∧ B ≠ I.pot y) := by sorry

end MinCostMaj
