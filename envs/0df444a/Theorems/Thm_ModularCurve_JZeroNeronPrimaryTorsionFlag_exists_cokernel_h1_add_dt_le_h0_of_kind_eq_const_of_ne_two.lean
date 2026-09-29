-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_cokernel_h1_add_dt_le_h0_of_kind_eq_const_of_ne_two
-- name    : ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_h1_add_dt_le_h0_of_kind_eq_const_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/f8d31f47-c9ac-51ad-a968-ed713d480f84
-- title:
--   Const-kind layer: l₁ + dₜ ≤ l₀ at odd q
-- statement:
--   Let $p$ and $q$ be primes with $q \neq 2$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ satisfying `LiesOverPrime p`, i.e. the image of $p$ lies in the non-units of $A$, and let $C$ be a Néron core `JZeroNeronPrimaryTorsionCore p q A hA` for the $q$-primary Eisenstein torsion. Fix $m$ and a flag `flag : JZeroNeronPrimaryTorsionFlag p q A hA C m`, whose data include sheaves $F_0, \dots, F_n$ of abelian groups on the small fppf site of $\operatorname{Spec}\mathbb Z$ with monomorphisms `incl` into the next term, a label `kind` for each step, and an increasing family `genericStep` of Galois-stable subgroups of $\mathrm{JZero}\,p$ interpolating between $\bot$ and `eisensteinPrimaryTorsionBar p q m`. Fix a step $i$ whose kind is `const`. Let $L$ be an fppf abelian sheaf on $\operatorname{Spec}\mathbb Z$ and $pr : F_{i+1} \to L$ a morphism with $\mathrm{incl}_i$ followed by $pr$ zero, such that the resulting short complex $F_i \to F_{i+1} \to L$ is short exact. Let $dt \in \mathbb N$ be such that the subgroup `jZeroToricTorsion p A (q ^ m)` — the $q^m$-torsion of $\mathrm{JZero}\,p$ intersected with the image of the inertia-invariant points at $A$ under multiplication by `eisensteinNumerator p` — meets `genericStep` at $i+1$ in a finite group of order $q^{dt}$ times that of its intersection with `genericStep` at $i$. Then there are $l_0, l_1 \in \mathbb N$ with $\#H^0_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z, L) = q^{l_0}$, $\#H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z, L) = q^{l_1}$ and $l_1 + dt \le l_0$ as integers.
--
--   This is the numerical estimate for a constant-type Jordan–Hölder layer of the $q$-primary Eisenstein torsion of $J_0(p)$ in the style of Mazur's analysis of finite flat group schemes over $\mathbb Z$, the oddness of $q$ being essential. It feeds into [`ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_h1_sub_h0_add_ite_kind_le_dg_sub_dt_of_ne_two`](thm.html#ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_h1_sub_h0_add_ite_kind_le_dg_sub_dt_of_ne_two), which assembles the layerwise bounds over the whole flag.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_cokernel_h1_add_dt_le_h0_of_kind_eq_const_of_ne_two.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_h1_add_dt_le_h0_of_kind_eq_const_of_ne_two
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin flag.n)
    (hk : flag.kind i = JZeroFlagLayerKind.const)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (pr : flag.F i.succ ⟶ L) (hzero : flag.incl i ≫ pr = 0)
    (hses : (ShortComplex.mk (flag.incl i) pr hzero).ShortExact)
    (dt : ℕ)
    (ht : Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ flag.genericStep i.succ)
        = q ^ dt * Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ flag.genericStep i.castSucc)) :
    ∃ l0 l1 : ℕ,
      Nat.card (fppfCohomology specInt L 0) = q ^ l0 ∧
      Nat.card (fppfCohomology specInt L 1) = q ^ l1 ∧
      (l1 : ℤ) + dt ≤ l0 := by sorry
