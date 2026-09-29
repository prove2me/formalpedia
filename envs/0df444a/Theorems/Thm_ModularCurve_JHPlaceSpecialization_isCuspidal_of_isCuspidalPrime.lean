-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_isCuspidalPrime
-- name    : ModularCurve.JHPlaceSpecialization.isCuspidal_of_isCuspidalPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/6d709fd0-802a-5988-80db-a9d08b7a4a00
-- title:
--   Cuspidality for j from cuspidality for j(qᵖ)
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$, and let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that $p$ is a non-unit of $A$, and let $W$ be a place of the function field $F_M =$ `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ — the latter being the intermediate field of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `xHFunctionField M H`, a place being a proper valuation subring containing the image of $\overline{\mathbb{Q}}$ and whose ring is a principal ideal ring. Assume `IsCuspidal'` for $W$: for every $x \in F_M$ whose Laurent expansion is $j(q^p)$, i.e. equals `qExpand` of the $q$-expansion `jqModC` of the modular invariant at exponent $p$, and for every $a \in A$, one has $\operatorname{ord}_W\!\big(x - a\big) \le 0$. The conclusion is `IsCuspidal` for $W$: for every $x \in F_M$ whose Laurent expansion is `jqModC` itself, that is $j(q)$, and every $a \in A$, again $\operatorname{ord}_W\!\big(x - a\big) \le 0$.
--
--   This is the passage between the two spellings of the cuspidal region occurring in the place-specialisation package for $X_H(M)$ at a prime $p$ dividing $M$: the primed predicate, formulated with $j(q^p)$, implies the unprimed one, formulated with $j$. The mathematical content is the integrality of $j$ over $\mathbb{Z}[j(q^p)]$ furnished by the modular polynomial $\Phi_p$, which is monic in each variable and vanishes at $(j, j(q^p))$; the result is used by the prolongation-datum lemmas and by the side/cusp-geometry statements for the model of $X_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_isCuspidalPrime.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.isCuspidal_of_isCuspidalPrime
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hW : JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) W) :
    (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) W := by sorry
