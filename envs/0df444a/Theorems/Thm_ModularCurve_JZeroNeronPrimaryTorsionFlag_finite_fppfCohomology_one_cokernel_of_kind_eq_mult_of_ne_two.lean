-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_finite_fppfCohomology_one_cokernel_of_kind_eq_mult_of_ne_two
-- name    : ModularCurve.JZeroNeronPrimaryTorsionFlag.finite_fppfCohomology_one_cokernel_of_kind_eq_mult_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/76297092-6dea-53aa-a60d-68c1c3e54800
-- title:
--   Finiteness of H¹_{fppf} for multiplicative flag layers
-- statement:
--   Fix primes $p$ and $q$ with $q \neq 2$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a nonunit of $A$ (the predicate `LiesOverPrime`). Let $C$ be a core datum `JZeroNeronPrimaryTorsionCore p q A hA`, which packages for each $m$ a sheaf of abelian groups $\mathcal{J}_m = C.\mathcal{J}\,m$ on the small fppf site of $\operatorname{Spec}\mathbb{Z}$ (the site of $\mathbb{Z}$-schemes that are flat and locally of finite presentation, with the fppf topology) together with a flat $\mathbb{Z}$-Hopf algebra $H_m$ of finite type whose points give the sections of $\mathcal{J}_m$, the identification of its geometric points with the $q$-primary Eisenstein torsion subgroup of $J_0(p)$, and the remaining compatibilities. Fix $m$ and a flag datum `flag : JZeroNeronPrimaryTorsionFlag p q A hA C m`, i.e. a chain $F_0 \to F_1 \to \cdots \to F_n$ of subsheaves of $\mathcal{J}_m$ arising from a chain of Hopf quotients $G_i$ of $H_m$, with $F_n \cong \mathcal{J}_m$, trivial bottom layer, and a layer label `flag.kind`. Let $i < n$ be an index whose label `flag.kind i` is `JZeroFlagLayerKind.mult`. Let $L$ be a sheaf of abelian groups on that site and $\mathrm{pr} : F_{i+1} \to L$ a morphism with $\mathrm{incl}_i$ followed by $\mathrm{pr}$ zero, such that the resulting short complex $F_i \to F_{i+1} \to L$ is short exact. Then the abelian group $H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb{Z}, L)$ is finite.
--
--   This is the multiplicative-kind case of the per-layer input to Mazur's dévissage for the finiteness of $H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb{Z}, \mathcal{J}_m)$, where the layer is realised as the sheaf of points of the Hopf kernel of the transition $G_{i+1} \to G_i$ and is of $\mu$-type over the odd prime $q$. It is consumed, alongside the constant-kind case, by [`ModularCurve.finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore_of_ne_two`](thm.html#ModularCurve.finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_finite_fppfCohomology_one_cokernel_of_kind_eq_mult_of_ne_two.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.finite_fppfCohomology_one_cokernel_of_kind_eq_mult_of_ne_two
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin flag.n)
    (hk : flag.kind i = JZeroFlagLayerKind.mult)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (pr : flag.F i.succ ⟶ L) (hzero : flag.incl i ≫ pr = 0)
    (hses : (ShortComplex.mk (flag.incl i) pr hzero).ShortExact) :
    Finite (fppfCohomology specInt L 1) := by sorry
