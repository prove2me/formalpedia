-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_isZeroSide
-- name    : ModularCurve.JHPlaceSpecialization.isCuspidal_of_isZeroSide
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/7fc0eb02-c420-567b-8ba4-466e20986156
-- title:
--   Zero-side places of X_H(M) are cuspidal
-- statement:
--   Let $p$ be a prime, let $M\ge 1$, let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, with residue field $\kappa(A)$. Write $F =$ `xHFunctionFieldBar M H` for the intermediate field of $\overline{\mathbb{Q}} \subseteq \overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the $q$-expansion function field of $X_H(M)$, and let $W$ be a place of $F$ over $\overline{\mathbb{Q}}$, that is, a valuation subring of $F$ containing $\overline{\mathbb{Q}}$, distinct from $F$, and a principal ideal ring. Assume $W$ lies on the zero side, i.e. both: (i) for every $x \in F$ whose Laurent expansion is $\mathrm{qExpand}_p(j(q)) = j(q^{p})$ and every $a \in A$ one has $\operatorname{ord}_W\bigl(x - a\bigr) \le 0$; and (ii) there are $x, x' \in F$ with Laurent expansions $j(q)$ and $j(q^{p})$ respectively, and a $\tau \in A$ whose residue in $\kappa(A)$ is $1$, such that $x/x'^{\,p}$ lies in the valuation subring of $W$ and has residue the image of $\tau$ in the residue field of $W$. Then $W$ is cuspidal in the sense that for every $x \in F$ with Laurent expansion $j(q)$ and every $a \in A$ one has $\operatorname{ord}_W\bigl(x - a\bigr) \le 0$; that is, $j$ takes no $A$-integral value at $W$.
--
--   This transfers the defining non-integrality property of the zero side of the cuspidal region from $j(q^{p})$ to $j(q)$, so that a zero-side place of the $\overline{\mathbb{Q}}$-function field of $X_H(M)$ is a cusp for $j$ itself. It is used in the analysis of the Deligne–Rapoport model of $X_H(M)$ at $p$, in the lemmas about prolongation data which identify residue carriers and vertical units on the reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_isZeroSide.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.isCuspidal_of_isZeroSide
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hW : JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) W) :
    JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) W := by sorry
