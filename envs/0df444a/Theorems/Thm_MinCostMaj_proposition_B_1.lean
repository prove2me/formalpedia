-- Prove2me | Theorems.Thm_MinCostMaj_proposition_B_1
-- name    : MinCostMaj.proposition_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:15:41.197459+00:00
-- url     : https://prove2.me/theorems/163c2f6c-aece-462c-b8d5-69c9ca2d9e4c
-- title:
--   Proposition B.1 — (2,3)-consistency gives the ambient instance
-- statement:
--   Let $R$ be a finite simplified instance ($R_{yx}=R_{xy}^{-1}$, $R_{xx}$ contained in the diagonal) and let $J$ be the result of the (2,3)-consistency preprocessing: the largest (2,3)-consistent family contained in $R$, with potatoes $A^J_x=\{a:(a,a)\in R^J_{xx}\}$. Then
--
--   1. the preprocessing is solution-preserving: an assignment satisfies every $R_{xy}$ iff it is a solution of $J$;
--   2. if no potato of $J$ is empty, $J$ is arc-consistent and cycle consistent (and its constraints follow the opposite-readings convention);
--   3. $J$ satisfies the (2,3)-condition, the stopping rule of the procedure.
--
--   $J$ is the ambient cycle-consistent instance on which the LP is solved.
--
--   Differences from the source:
--   - encoding: repeatedly delete tuples until the (2,3)-condition holds; denote the resulting instance by J → J is the largest (2,3)-consistent subfamily of R; the conclusion also records that J satisfies the (2,3)-condition and the opposite-readings convention; reason: the deletion procedure ends at this family whatever the order; these are properties the paper asserts of J by construction
--   - reading: instances → finite variable and value types; reason: instances are finite inputs
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Proposition B.1, p.19, with the preprocessing on p.10 (PDF pp.11, 20)

import Mathlib
import Definitions.Def_MinCostMaj_BinInst
import Definitions.Def_MinCostMaj_Pattern
import Definitions.Def_MinCostMaj_SimpInst

namespace MinCostMaj

/-- **Proposition B.1** ((2,3)-consistency gives the ambient instance), p.19 (PDF p.20).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Proposition B.1, p.19: "The (2, 3)-consistency preprocessing is solution-preserving.
Moreover, if no potato is emptied, then J is arc-consistent and cycle consistent." The
preprocessing (§5, p.10): "we repeatedly delete tuples until, for every triple of variables x, y, z
and every (a, b) ∈ Rxy, there is c ∈ Az such that (a, c) ∈ Rxz and (b, c) ∈ Ryz. The potatoes are
the projections of the remaining binary relations. … denote the resulting instance by J."

For a simplified instance `R` (one relation per ordered pair, `R_yx = −R_xy`, `R_xx` diagonal),
`J` is `simpToBin (greatest23 R)`: the largest (2,3)-consistent subfamily, with potatoes read from
its diagonal. Conclusions: (i) the assignments satisfying every `R_xy` are exactly the solutions
of `J`; (ii) if every potato of `J` is nonempty, `J` follows the opposite-readings convention, is
arc-consistent and is cycle consistent; (iii) `J` satisfies the stopping condition of the
procedure.

**Formalization Note.** The deletion procedure is represented by its result, the largest
(2,3)-consistent subfamily (see `greatest23`). Clause (ii)'s symmetry records that `J` is an
instance in the sense of §3. Finite variables and domain. -/
theorem proposition_B_1 {V D : Type*} [Finite V] [Finite D] (R : V → V → Set (D × D))
    (hR : IsSimplified R) :
    (∀ α : V → D, (∀ x y, (α x, α y) ∈ R x y) ↔ (simpToBin (greatest23 R)).IsSolution α) ∧
    ((∀ x, (simpPot (greatest23 R) x).Nonempty) →
      (simpToBin (greatest23 R)).IsSymm ∧ (simpToBin (greatest23 R)).IsCycleConsistent) ∧
    Is23Consistent (greatest23 R) := by sorry

end MinCostMaj
