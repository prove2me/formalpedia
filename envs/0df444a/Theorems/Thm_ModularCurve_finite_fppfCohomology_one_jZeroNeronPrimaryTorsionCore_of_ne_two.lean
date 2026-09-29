-- Prove2me | Theorems.Thm_ModularCurve_finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore_of_ne_two
-- name    : ModularCurve.finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/699bdede-5163-5f37-8323-1049dd3f2395
-- title:
--   Finiteness of H¹_{fppf}(Specℤ,mathcal J_m) for odd q
-- statement:
--   Let $p$ and $q$ be primes with $q \neq 2$, let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbb Q}$ lies in the non-units of $A$, and let $C$ be a term of the structure `JZeroNeronPrimaryTorsionCore p q A hA`. Such a $C$ consists of a family $\mathcal J_m$ ($m \in \mathbb N$) of abelian sheaves on the small fppf site of $\operatorname{Spec}\mathbb Z$ together with commutative $\mathbb Z$-Hopf algebras $H_m$ of finite type and flat over $\mathbb Z$, such that $\mathbb Q^{(\ell)} \otimes_{\mathbb Z} H_m$ is a finite module over the subring $\mathbb Q^{(\ell)} \subset \mathbb Q$ of rationals with denominator coprime to $\ell$, for every prime $\ell \neq p$; isomorphisms, natural in $U$, of the sections $\mathcal J_m(U)$ with the additive group on the convolution monoid of $\mathbb Z$-algebra maps $H_m \to \Gamma(U_{\mathrm{left}},\top)$; identifications, compatible with convolution and with the Galois action, of the $\overline{\mathbb Q}$-points of $H_m$ with the subgroup of $J_0$ (the degree-zero Picard group of the modular function field) consisting of $q^m$-torsion points annihilated by some power of the Eisenstein maximal ideal, and of the $A$-points with the intersection of that subgroup with the toric $q^m$-torsion; quotient sheaves $Q_m$ fitting into short exact sequences $0 \to \mathcal J_m \to \mathcal J_{m+1} \to Q_m \to 0$; and Kummer-row data. Then for every $m$ the degree-one fppf cohomology group $H^1(\operatorname{Spec}\mathbb Z, \mathcal J_m)$, computed as the sheaf cohomology of $\mathcal J_m$ on the small fppf site, is finite.
--
--   This is the finiteness of the first fppf cohomology over $\operatorname{Spec}\mathbb Z$ of the Eisenstein-primary $q^m$-torsion sheaves attached to the Néron model of $J_0(p)$, in the spirit of Mazur's analysis of quasi-finite flat groups over $\operatorname{Spec}\mathbb Z$; the restriction to odd $q$ is what allows the layers of the filtration to be classified as constant or multiplicative. It is the odd-$q$ instance used in the derivation of the general statement [`ModularCurve.finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore`](thm.html#ModularCurve.finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore_of_ne_two.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring

theorem ModularCurve.finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore_of_ne_two (p : ℕ) [Fact p.Prime]
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) :
    ∀ m : ℕ, Finite (fppfCohomology specInt (C.𝒥 m) 1) := by sorry
