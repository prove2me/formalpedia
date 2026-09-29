-- Prove2me | Theorems.Thm_ModularCurve_exists_finset_forall_isCentreOf_unique_ord_eq_one
-- name    : ModularCurve.exists_finset_forall_isCentreOf_unique_ord_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/bfd2527e-aac8-51be-a766-a58bec4c2381
-- title:
--   Almost all affine places of the level-N fibre are smooth
-- statement:
--   Let $q$ be a prime, let $k$ be an algebraically closed field of characteristic $q$, let $N \geq 1$ and assume $q \nmid N$. Write $F_N =$ `modularFunctionFieldC k N` for the intermediate field of the Laurent series field $k((q))$ generated over $k$ by the two elements `jqModC k` and `jqNModC k N`, and let $\tilde\jmath =$ `jGeomGen k N` and $\tilde\jmath_N =$ `jNGeomGen k N` denote these two generators viewed in $F_N$. A place of $F_N$ over $k$ is a valuation subring of $F_N$ which contains $k$, is not all of $F_N$, and is a principal ideal ring; $\operatorname{ord}_v$ is the associated normalised integer valuation. The assertion is that there exists a finite set $B$ of such places with the following property: for every place $v \notin B$ such that both $\tilde\jmath$ and $\tilde\jmath_N$ lie in the valuation subring of $v$, there is a pair $c = (c_1,c_2) \in k \times k$ with $\operatorname{ord}_v(\tilde\jmath - c_1) > 0$ and $\operatorname{ord}_v(\tilde\jmath_N - c_2) > 0$, such that $v$ is the unique place of $F_N$ with these two positivity properties for this $c$, and such that moreover $\operatorname{ord}_v(\tilde\jmath - c_1) = 1$ or $\operatorname{ord}_v(\tilde\jmath_N - c_2) = 1$.
--
--   This is the statement that all but finitely many affine places of the level-$N$ fibre in characteristic $q \nmid N$ are smooth points of its affine plane model cut out by the modular equation $\Phi_N(\tilde\jmath,\tilde\jmath_N) = 0$: such a place is the only one centred at its pair of coordinate values, and one of the two coordinate functions is a uniformiser there. It is used in the construction of place specialisations in general position, where the inertia action at the chosen places must be controlled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finset_forall_isCentreOf_unique_ord_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_finset_forall_isCentreOf_unique_ord_eq_one
    (q : ℕ) (k : Type*) [Field k] [Fact q.Prime] [CharP k q] [IsAlgClosed k]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) :
    ∃ B : Finset (Place k ↥(modularFunctionFieldC k N)),
      ∀ v ∉ B, IsAffineGeomPlace k N v →
        ∃ c : k × k, IsCentreOf k N c v ∧
          (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
          (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
            v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1) := by sorry
