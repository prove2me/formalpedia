-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_not_isInftySide_of_isZeroSide
-- name    : ModularCurve.JHPlaceSpecialization.not_isInftySide_of_isZeroSide
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/e0c5d384-5d45-5f5c-a880-39e6bfe024f8
-- title:
--   Zero side and infinity side of the cusps are disjoint
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbf{Z}/M)^{\times}$, and a valuation subring $A$ of $\overline{\mathbf{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime p`, i.e. the image of $p$ lies in the nonunits of $A$. Let $W$ be a place of the function field $FM =$ `xHFunctionFieldBar M H` over $\overline{\mathbf{Q}}$ (a proper valuation subring of $FM$ containing $\overline{\mathbf{Q}}$ whose ideals are principal). Assume $W$ is on the zero side: first, for every $x \in FM$ whose Laurent expansion is `qExpand` $p$ of `jqModC` (the $q$-expansion of $j$ in $q^{p}$) and every $a \in A$ one has $\operatorname{ord}_W(x - a) \le 0$; second, there are $x, x' \in FM$ with Laurent expansions `jqModC` and `qExpand` $p$ `jqModC` respectively, and $\tau \in A$ with residue $1$, such that $x / x'^{p}$ lies in the valuation ring of $W$ with residue the image of $\tau$. The conclusion is that $W$ is not on the infinity side: it is not the case that both $\operatorname{ord}_W(x - a) \le 0$ for all $x$ with expansion `jqModC` and all $a \in A$, and that for some such pair $x, x'$ and some $\tau \in A$ of residue $1$ the element $x' / x^{p}$ has $W$-value $\tau$.
--
--   This is the disjointness half of the cuspidal dichotomy for $X_H(M)$ in characteristic $p$: the two branches through a cusp of the fibre, distinguished by the unit parameters $j/j(q^{p})^{p}$ and $j(q^{p})/j^{p}$, cannot both specialise to $1$ at the same place, the obstruction being the relation $(j/j(q^p)^p)\,(j(q^p)/j^p) = (j\, j(q^p))^{1-p}$. It is used in the prolongation-datum lemmas that orient places on the two components and control residues and poles in the associated Riemann–Roch spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_not_isInftySide_of_isZeroSide.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.not_isInftySide_of_isZeroSide
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hW : JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) W) :
    ¬ JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W := by sorry
