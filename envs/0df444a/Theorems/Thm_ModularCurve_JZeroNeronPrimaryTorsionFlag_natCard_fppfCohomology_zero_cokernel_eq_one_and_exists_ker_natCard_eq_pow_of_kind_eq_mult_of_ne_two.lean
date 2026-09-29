-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two
-- name    : ModularCurve.JZeroNeronPrimaryTorsionFlag.natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/ad6d08b3-5974-5d83-9f49-d661e19d7adc
-- title:
--   Multiplicative layers: trivial H⁰ and μ_q-kernel bound
-- statement:
--   Let $p$ and $q$ be primes with $q \neq 2$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ (the hypothesis `LiesOverPrime`), let $C$ be a `JZeroNeronPrimaryTorsionCore` for $p,q,A$ — the package consisting of fppf abelian sheaves $\mathcal J_m$ on the small fppf site of $\operatorname{Spec}\mathbb Z$, flat finite-type Hopf $\mathbb Z$-algebras $H_m$ representing their sections, and the identification of the generic points of $H_m$ with `eisensteinPrimaryTorsionBar` $p\,q\,m$ — and fix $m$ and a flag `flag` of type `JZeroNeronPrimaryTorsionFlag` over $C$ at level $m$: a chain $F_0 \to \dots \to F_n \cong \mathcal J_m$ of subsheaves with Hopf-algebra quotients $G_i$ of $H_m$ and an increasing family `genericStep` of Galois-stable subgroups of `JZero` $p$ from $\bot$ to `eisensteinPrimaryTorsionBar` $p\,q\,m$. Fix a step $i < n$ whose label satisfies `flag.kind i = mult`, and let $L$ be an fppf abelian sheaf together with $\mathrm{pr} : F_{i+1} \to L$ such that $\mathrm{incl}_i$ followed by $\mathrm{pr}$ is zero and $0 \to F_i \to F_{i+1} \to L \to 0$ is short exact. Assume, for some $d_t \in \mathbb N$, that the order of $\,$`jZeroToricTorsion` $p\,A\,(q^m)\, \sqcap\,$`genericStep` $(i+1)$ equals $q^{d_t}$ times that of `jZeroToricTorsion` $p\,A\,(q^m)\, \sqcap\,$`genericStep` $i$, where `jZeroToricTorsion` $p\,A\,M$ is the intersection of the $M$-torsion of `JZero` $p$ with the image of the inertia-invariant points under multiplication by `eisensteinNumerator` $p$. Then $H^0$ of $L$ on the small fppf site of $\operatorname{Spec}\mathbb Z$ (the Ext-theoretic `fppfCohomology` in degree $0$) has exactly one element, and there exist $d_k \in \mathbb N$ with $d_k + d_t \le 1$, an fppf abelian sheaf $K$ whose underlying presheaf is isomorphic to the restriction along $\operatorname{Spec}\mathbb Z$-forgetful functors of the presheaf underlying [`FppfKummerSES.muPAbelianSheafLifted`](def/AlgebraicGeometry_FppfKummerProp17.html#L608) $q$ (the kernel of the $q$-power map on the lifted multiplicative-group sheaf, i.e. $\mu_q$), and a morphism $f : L \to K$ such that the kernel of the induced map on $H^1$ has exactly $q^{d_k}$ elements.
--
--   This is the multiplicative-type case of the layer-by-layer analysis of the $q$-primary Eisenstein torsion of $J_0(p)$ in the style of Mazur, comparing a Jordan–Hölder layer of the associated finite flat group scheme with $\mu_q$ over $\operatorname{Spec}\mathbb Z$; the restriction to odd $q$ is what makes the comparison with $\mu_q$ rigid. It feeds the cohomological bound [`ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_h1_add_dt_le_h0_add_one_of_kind_eq_mult_of_ne_two`](thm.html#ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_h1_add_dt_le_h0_add_one_of_kind_eq_mult_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin flag.n)
    (hk : flag.kind i = JZeroFlagLayerKind.mult)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (pr : flag.F i.succ ⟶ L) (hzero : flag.incl i ≫ pr = 0)
    (hses : (ShortComplex.mk (flag.incl i) pr hzero).ShortExact)
    (dt : ℕ)
    (ht : Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ flag.genericStep i.succ)
        = q ^ dt * Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ flag.genericStep i.castSucc)) :
    Nat.card (fppfCohomology specInt L 0) = 1 ∧
    ∃ dk : ℕ, dk + dt ≤ 1 ∧
      ∃ (K : Sheaf (smallFppfTopology specInt) Ab.{1})
        (_ : K.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
            (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj)
        (f : L ⟶ K), Nat.card ↥(fppfCohomologyMap specInt f 1).ker = q ^ dk := by sorry
