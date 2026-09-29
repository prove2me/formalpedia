-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_finite_fppfCohomology_one_layer_two
-- name    : ModularCurve.JZeroNeronPrimaryTorsionFlag.finite_fppfCohomology_one_layer_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/76c6e9c8-1b7f-54e5-ba31-74fcf3f26a28
-- title:
--   Finiteness of fppf H¹ of a flag layer at q=2
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ with `A.LiesOverPrime p`, that is, the image of $p$ lies in the non-units of $A$. Let $C$ be a `JZeroNeronPrimaryTorsionCore p 2 A hA`, let $m$ be a natural number, and let `flag` be a `JZeroNeronPrimaryTorsionFlag p 2 A hA C m`: a length `flag.n` filtration $F_0 \to F_1 \to \cdots \to F_{n}$ by abelian sheaves on the small fppf site of $\operatorname{Spec}\mathbb Z$ (the site of $\mathbb Z$-schemes that are flat and locally of finite presentation, with the associated small topology), each $F_i$ embedded by a monomorphism $\iota_i$ into the sheaf $C.\mathcal J\,m$ compatibly with the inclusions, whose sections over $U$ are identified additively with the `WithConv` group of $\mathbb Z$-algebra maps $G_i \to \Gamma(U_{\mathrm{left}},\top)$ for a chain of commutative flat finite-type $\mathbb Z$-Hopf algebras $G_i$ with surjections $G_{i+1} \to G_i$ and surjections from $C.H\,m$, with $\iota_{n}$ an isomorphism, together with an associated monotone Galois-stable filtration `genericStep` of subgroups of `JZero p` running from $\bot$ to `eisensteinPrimaryTorsionBar p 2 m`, and further data. Let $i <$ `flag.n`, let $L$ be an abelian sheaf on the same site, and let $pr : F_{i+1} \to L$ satisfy `flag.incl i ≫ pr = 0` and make $0 \to F_i \to F_{i+1} \to L \to 0$ short exact. Then the type `fppfCohomology specInt L 1`, the first fppf cohomology group $H^1(\operatorname{Spec}\mathbb Z, L)$, is finite.
--
--   This is the per-layer finiteness input to Mazur's dévissage of the Néron model of the $\mathfrak P$-primary $2$-power Eisenstein torsion of $J_0(p)$, in the case $q = 2$, where a graded piece of the flag has Hopf kernel of order $2$ and no further hypothesis on the type of the layer is needed. It is used by [`ModularCurve.finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore`](thm.html#ModularCurve.finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore), which assembles the layers into finiteness of $H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z, \mathcal J_m)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_finite_fppfCohomology_one_layer_two.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.finite_fppfCohomology_one_layer_two
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p 2 A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p 2 A hA C m) (i : Fin flag.n)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (pr : flag.F i.succ ⟶ L) (hzero : flag.incl i ≫ pr = 0)
    (hses : (ShortComplex.mk (flag.incl i) pr hzero).ShortExact) :
    Finite (fppfCohomology specInt L 1) := by sorry
