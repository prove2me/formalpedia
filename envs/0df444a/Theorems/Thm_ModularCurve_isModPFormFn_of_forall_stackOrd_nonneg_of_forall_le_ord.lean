-- Prove2me | Theorems.Thm_ModularCurve_isModPFormFn_of_forall_stackOrd_nonneg_of_forall_le_ord
-- name    : ModularCurve.isModPFormFn_of_forall_stackOrd_nonneg_of_forall_le_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/a50548eb-d0cb-5a12-931e-13760da30269
-- title:
--   Order conditions at affine places and cusps imply integrality
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $N \ge 1$ be an integer with $p \nmid N$, and let $K$ be an algebraically closed field of characteristic $p$. Let $m$ be a natural number and let $G$ be a nonzero element of `modularFunctionFieldC K N`, the intermediate field of $K((q))$ generated over $K$ by the two $q$-series $\bar{j}(q) =$ `jqModC K` and $\bar{j}(q^N) =$ `jqNModC K N`. Places $x$ here are valuation subrings of this field containing $K$, distinct from the whole field and principal ideal rings, with $\operatorname{ord}_x$ the associated normalised valuation. Two hypotheses are imposed. First, at every place $x$ satisfying `IsAffineGeomPlace`, i.e. such that both $\bar{j}(q)$ and $\bar{j}(q^N)$ lie in the valuation subring of $x$, the quantity $$\mathrm{placeWidth}_N(x)\cdot \operatorname{ord}_x G + m\bigl(w(x) - 1\bigr) \ge 0,$$ where $w(x) =$ `jWidth` of the residue value $x(\bar j)$ (namely $3$ if it is $0$, $2$ if it is $1728$, and $1$ otherwise) and $\mathrm{placeWidth}_N(x)$ is the natural-number quotient of $w(x)$ by `placeRamificationJ N x`. Second, at every place $x$ with $\operatorname{ord}_x \bar{j}(q) < 0$ one has $m\cdot(-\operatorname{ord}_x \bar{j}(q)) \le \operatorname{ord}_x G$. The conclusion is `IsModPFormFn K m G` for $G$ viewed in $K((q))$: the element $G^6\,\bar{j}^{4m}(\bar{j} - 1728)^{3m}$ is integral over the subring $K[\bar{j}]$ of $K((q))$, and $G^2\,\bar{j}^{m}(\bar{j} - 1728)^{m}$ is integral over $K[\bar{j}^{-1}]$.
--
--   This is one direction of the dictionary between the integrality description of mod $p$ modular functions of weight $2m$ on the $j$-line (integrality over $K[\bar j]$ and over $K[\bar j^{-1}]$ after clearing the elliptic-point and cusp denominators) and the place-by-place order conditions on the level-$N$ modular curve in characteristic $p$, the orders being those of the weight-$2m$ object $G\,(d\bar j)^{\otimes m}$ on the moduli stack. It is used when mod $p$ forms are produced from functions with prescribed orders, for instance in the passage between Riemann–Roch spaces and spaces of mod $p$ cusp forms and in the Hecke-theoretic constructions built on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isModPFormFn_of_forall_stackOrd_nonneg_of_forall_le_ord.lean

import Mathlib
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.isModPFormFn_of_forall_stackOrd_nonneg_of_forall_le_ord
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type*) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (m : ℕ) (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0)
    (haff : ∀ x : Place K (modularFunctionFieldC K N), IsAffineGeomPlace K N x →
        0 ≤ stackOrd N (m : ℤ) G x)
    (hcusp : ∀ x : Place K (modularFunctionFieldC K N), x.ord (jGeomGen K N) < 0 →
        (m : ℤ) * (-(x.ord (jGeomGen K N))) ≤ x.ord G) :
    IsModPFormFn K m (G : LaurentSeries K) := by sorry
