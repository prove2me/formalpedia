-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_cokernel_dt_le_h0_and_h1_add_da_le_one_two
-- name    : ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_dt_le_h0_and_h1_add_da_le_one_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/214e549a-061a-5cf9-8830-678f4dd1199b
-- title:
--   Cohomology bounds for a layer of the 2-primary flag
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (the predicate `LiesOverPrime`), let $C$ be a `JZeroNeronPrimaryTorsionCore` datum for $p$, $q=2$, $A$, let $m$ be a natural number, and let `flag` be a `JZeroNeronPrimaryTorsionFlag` for these data: a finite chain of finite-type flat Hopf $\mathbb{Z}$-algebras $G_j$ with surjections from $C.H\,m$, a chain of subsheaves $F_j$ of the fppf sheaf $C.\mathcal{J}\,m$ on the small fppf site of $\operatorname{Spec}\mathbb{Z}$ whose sections over $U$ are identified with the $\mathbb{Z}$-algebra maps $G_j \to \Gamma(U,\mathcal{O})$, and an increasing filtration `genericStep` of $\operatorname{Pic}^0$ of the modular function field tower (the group $\mathrm{JZero}\,p$) by Galois-stable subgroups running from $\bot$ to `eisensteinPrimaryTorsionBar p 2 m`. Fix a step $i$, an fppf sheaf of abelian groups $L$ on $\operatorname{Spec}\mathbb{Z}$ and a map $\mathrm{pr} : F_{i+1} \to L$ with $\mathrm{incl}_i$ followed by $\mathrm{pr}$ zero, such that the resulting short complex $F_i \to F_{i+1} \to L$ is short exact, so $L$ is the $i$-th graded piece. Let $d_t, d_a$ be natural numbers such that the intersection of `jZeroToricTorsion p A (2 ^ m)` (the $2^m$-torsion of $\mathrm{JZero}\,p$ intersected with the image of the inertia-invariant points under multiplication by `eisensteinNumerator p`) with the $(i+1)$-st filtration step has cardinality $2^{d_t}$ times its intersection with the $i$-th step, and such that the number of $\mathbb{Z}$-algebra maps $G_{i+1} \to \overline{\mathbb{F}_2}$ is $2^{d_a}$ times the number for $G_i$. Then there exist natural numbers $l_0, l_1$ with $\#H^0_{\mathrm{fppf}}(\operatorname{Spec}\mathbb{Z}, L) = 2^{l_0}$, $\#H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb{Z}, L) = 2^{l_1}$, $d_t \le l_0$ and $l_1 + d_a \le 1$.
--
--   This is the layer-by-layer cohomological input for the analysis of the $2$-primary Eisenstein torsion of $J_0$ over $\operatorname{Spec}\mathbb{Z}$, in the style of Mazur's tables for group schemes of order $2$ over $\mathbb{Z}$: each graded piece of the flag has fppf $H^0$ and $H^1$ of $2$-power order, with the toric jump bounded below by $H^0$ and the étale-at-$2$ jump bounded above by $1 - \dim H^1$. It feeds the numerical estimate [`ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_h1_sub_h0_add_da_le_dg_sub_dt_two`](thm.html#ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_h1_sub_h0_add_da_le_dg_sub_dt_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_cokernel_dt_le_h0_and_h1_add_da_le_one_two.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_dt_le_h0_and_h1_add_da_le_one_two
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p 2 A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p 2 A hA C m) (i : Fin flag.n)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (pr : flag.F i.succ ⟶ L) (hzero : flag.incl i ≫ pr = 0)
    (hses : (ShortComplex.mk (flag.incl i) pr hzero).ShortExact)
    (dt da : ℕ)
    (ht : Nat.card ↥(jZeroToricTorsion p A (2 ^ m) ⊓ flag.genericStep i.succ)
        = 2 ^ dt * Nat.card ↥(jZeroToricTorsion p A (2 ^ m) ⊓ flag.genericStep i.castSucc))
    (ha : Nat.card (flag.G i.succ →ₐ[ℤ] AlgebraicClosure (ZMod 2))
        = 2 ^ da * Nat.card (flag.G i.castSucc →ₐ[ℤ] AlgebraicClosure (ZMod 2))) :
    ∃ l0 l1 : ℕ,
      Nat.card (fppfCohomology specInt L 0) = 2 ^ l0 ∧
      Nat.card (fppfCohomology specInt L 1) = 2 ^ l1 ∧
      dt ≤ l0 ∧ l1 + da ≤ 1 := by sorry
