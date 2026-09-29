-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_finite_fppfCohomology_one_cokernel_of_kind_eq_const_of_ne_two
-- name    : ModularCurve.JZeroNeronPrimaryTorsionFlag.finite_fppfCohomology_one_cokernel_of_kind_eq_const_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/52248140-a7d5-5fbf-a625-3ec2acf4a60b
-- title:
--   Finiteness of H¹_{fppf} at a constant flag layer, q odd
-- statement:
--   Let $p$ and $q$ be primes with $q \neq 2$, let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense that $p$ is a non-unit of $A$ (`LiesOverPrime`), let $C$ be a `JZeroNeronPrimaryTorsionCore` for the data $p, q, A$, fix $m \in \mathbb N$, and let `flag` be a `JZeroNeronPrimaryTorsionFlag` for $C$ at level $m$: thus `flag` consists of flat finite-type $\mathbb Z$-Hopf algebras $G_0, \dots, G_n$ together with compatible surjections $\pi_j$ from $C.H\,m$ and surjections $G_{j+1} \to G_j$, of a chain $F_0 \to F_1 \to \cdots \to F_n$ of abelian sheaves on the small fppf site of $\operatorname{Spec}\mathbb Z$ (objects: schemes flat and locally of finite presentation over $\operatorname{Spec}\mathbb Z$) each monomorphing into $C.\mathcal J\,m$ with $F_n \cong C.\mathcal J\,m$, the sections of $F_j$ over $U$ being identified with the $\mathbb Z$-algebra maps $G_j \to \Gamma(U,\mathcal O_U)$ under convolution, compatibly with $\pi_j$, plus a generic filtration of the $(q^m)$-torsion Eisenstein-primary subgroup of $J_0(p)$ and a kind assignment to each step. Let $i < n$ be a step whose kind is `JZeroFlagLayerKind.const`, let $L$ be an abelian sheaf on the same site, and let $\mathrm{pr} : F_{i+1} \to L$ satisfy that the composite of $F_i \to F_{i+1}$ with $\mathrm{pr}$ is zero and that the resulting short complex $F_i \to F_{i+1} \to L$ is short exact. Then the first fppf cohomology group $H^1(\operatorname{Spec}\mathbb Z, L)$ is finite.
--
--   This is the constant-layer case of the dévissage that deduces finiteness of $H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z, \mathcal J_m)$ from finiteness for the successive quotients of a flag of the Néron $q^m$-torsion sheaf, in the hypothesis shape consumed by the chain argument. It is used in the proof of [`ModularCurve.finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore_of_ne_two`](thm.html#ModularCurve.finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_finite_fppfCohomology_one_cokernel_of_kind_eq_const_of_ne_two.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.finite_fppfCohomology_one_cokernel_of_kind_eq_const_of_ne_two
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin flag.n)
    (hk : flag.kind i = JZeroFlagLayerKind.const)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (pr : flag.F i.succ ⟶ L) (hzero : flag.incl i ≫ pr = 0)
    (hses : (ShortComplex.mk (flag.incl i) pr hzero).ShortExact) :
    Finite (fppfCohomology specInt L 1) := by sorry
