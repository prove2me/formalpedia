-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_isInftySide_or_isZeroSide_of_isCuspidal
-- name    : ModularCurve.JHPlaceSpecialization.isInftySide_or_isZeroSide_of_isCuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/8416a237-28bb-54b7-9c74-3604be42a888
-- title:
--   Cuspidal places lie on the ∞-side or the 0-side
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$, let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that $p$ is a non-unit of $A$. Let $W$ be a place of the field $F_M = \overline{\mathbb{Q}}\cdot F(\Gamma_H(M))$, the base change to $\overline{\mathbb{Q}}$ inside $\overline{\mathbb{Q}}((q))$ of the $\Gamma_H(M)$-function field, a place being a valuation subring containing $\overline{\mathbb{Q}}$, different from the whole field, and a principal ideal ring. Assume $W$ is cuspidal: for every $x \in F_M$ whose $q$-expansion is the series $j(q)$ and every $a \in A$, the order of $x - a$ at $W$ is at most $0$. The conclusion is a disjunction. Either $W$ is on the $\infty$-side: $W$ is cuspidal as above, and there are $x, x' \in F_M$ with $q$-expansions $j(q)$ and $j(q^p)$ respectively and an element $\tau \in A$ with residue $1$ in the residue field of $A$ such that $x'/x^{p}$ lies in the valuation subring of $W$ with residue the image of $\tau$; or $W$ is on the $0$-side: for every $x \in F_M$ with $q$-expansion $j(q^p)$ and every $a \in A$ the order of $x - a$ at $W$ is at most $0$, and there are $x, x'$ as before and $\tau \in A$ with residue $1$ such that $x/x'^{p}$ is $W$-integral with residue the image of $\tau$.
--
--   This is the $\Gamma_H(M)$ version of the dichotomy for the two components of the fibre at $p$ of the modular curve with $\Gamma_0(p)$-structure: a place in the cuspidal region, where $j$ attains no $A$-integral value, is distinguished by which of the two ratios $j(q^p)/j^p$ and $j/j(q^p)^p$ reduces to a unit congruent to $1$. It is invoked repeatedly in the prolongation-datum lemmas which orient places of the special fibre and compute orders and inertia behaviour there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_isInftySide_or_isZeroSide_of_isCuspidal.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.isInftySide_or_isZeroSide_of_isCuspidal
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hW : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) W) :
    JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W ∨
      JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) W := by sorry
