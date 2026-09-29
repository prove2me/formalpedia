-- Prove2me | Theorems.Thm_ModularCurve_nonempty_igusaDiamondDataX1C
-- name    : ModularCurve.nonempty_igusaDiamondDataX1C
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/573e4818-39de-576c-ac48-84197b355e17
-- title:
--   Existence of a diamond datum on the Igusa function field of X₁(M)
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $M \ge 5$ and $p \nmid M$, and let $k$ be an algebraically closed field of characteristic $p$. Let $w$ be an integral weight-one form for level $M$ over $k$: a modular form `w.form` of weight $1$ on $\Gamma_1(M)$, a power series `w.series` with integer coefficients whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of `w.form`, subject to the requirement that the reduction `intSeriesC k w.series`, the image of `w.series` in the Laurent series field $k((q))$, be nonzero. Put $a :=$ `w.hasseRootFn`$= ($`intSeriesC k w.series`$)^{-1} \in k((q))$ and let $K_0 :=$ `x1FunctionFieldC k M` be the $q$-expansion function field of $X_1(M)$ over $k$, i.e. `qExpFunctionFieldC k (Gamma1 M)`, an intermediate field of $k((q))$ over $k$. The assertion is that the type `IgusaCover.IgusaDiamondData p (-1) K₀ a` is nonempty: there exists a monoid homomorphism $b \mapsto \langle b\rangle$ from $(\mathbb{Z}/p)^\times$ to the group of $k$-algebra automorphisms of the field `igusaFunctionField K₀ a` (the Igusa function field attached to $K_0$ and $a$, which contains $a$) such that every $\langle b\rangle$ fixes each element of that field whose underlying Laurent series lies in $K_0$, and such that $\langle b\rangle a = \bar{b}^{-1}\, a$, where $\bar{b}^{-1}$ is the image of $b^{-1} \in (\mathbb{Z}/p)^\times$ under the ring homomorphism $\mathbb{Z}/p \to k$.
--
--   This provides the diamond (Kummer) action of $(\mathbb{Z}/p)^\times$ on the Igusa covering $\mathrm{Ig}(M;p)_k = K_0(a)$ of $X_1(M)_k$ in the $q$-expansion model, the automorphism attached to $b$ scaling the Hasse root function $a$ by $b^{-1}$ while fixing the function field of $X_1(M)_k$. It is used in the proof that $j$-type functions pulled back from the base do not lie in the Igusa function field in the non-divisibility case ([`ModularCurve.jqNModC_not_mem_igusaFunctionFieldX1C_of_not_dvd`](thm.html#ModularCurve.jqNModC_not_mem_igusaFunctionFieldX1C_of_not_dvd)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nonempty_igusaDiamondDataX1C.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionField
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.nonempty_igusaDiamondDataX1C
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (w : ModularCurve.IntegralWeightOneForm k M) :
    Nonempty (ModularCurve.IgusaDiamondDataX1C k M w p) := by sorry
