-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionCore_pow_nsmul_sections_eq_zero
-- name    : ModularCurve.JZeroNeronPrimaryTorsionCore.pow_nsmul_sections_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/3b7834a4-c804-5c9b-aeba-d803a316da90
-- title:
--   Multiplication by q^m annihilates the sheaves mathcal J_m
-- statement:
--   Let $p$ and $q$ be primes, let $A$ be a valuation subring of $\overline{\mathbb Q}$ satisfying `A.LiesOverPrime p`, i.e. the image of $p$ lies in the set of non-units of $A$, and let $C$ be a term of the structure `JZeroNeronPrimaryTorsionCore p q A hA`. Such a $C$ carries, among other data, a family of abelian sheaves $\mathcal J_m = C.\mathcal J\,m$ on the small fppf site of $\operatorname{Spec}\mathbb Z$ (coverings by morphisms that are flat and locally of finite presentation), together with commutative Hopf $\mathbb Z$-algebras $H_m = C.H\,m$ that are flat and of finite type over $\mathbb Z$, an identification of the sections of $\mathcal J_m$ over an object $U$ of the site with the convolution group of $\mathbb Z$-algebra homomorphisms $H_m \to \Gamma(U,\mathcal O_U)$, natural in $U$, an identification of the convolution group of $\mathbb Z$-algebra homomorphisms $H_m \to \overline{\mathbb Q}$ with the subgroup of $J_0(p)$ cut out by the kernel of multiplication by $q^m$ intersected with the $\mathfrak P$-primary part for the Eisenstein maximal ideal $\mathfrak P$, a Galois-equivariance and an $A$-valued analogue of this identification, short exact sequences relating $\mathcal J_m$, $\mathcal J_{m+1}$ and quotient sheaves $Q_m$, and Kummer-row data. The conclusion is that for every natural number $m$, every object $U$ of the small fppf site of $\operatorname{Spec}\mathbb Z$ and every section $s$ of the underlying presheaf of $\mathcal J_m$ over $U$, one has $q^m\cdot s = 0$.
--
--   This is the identity $[q^m] = 0$ on the $\mathfrak P$-primary part of the $q^m$-torsion, expressed on sections over an arbitrary object of the fppf site; equivalently, the Hopf-algebra identity asserting that the $q^m$-fold convolution power of any point of $H_m$ is the trivial point. It holds for every core of this type and is used in the computation of the order of the first fppf cohomology group, [`ModularCurve.JZeroNeronPrimaryTorsionCore.exists_natCard_fppfCohomology_one_eq_pow`](thm.html#ModularCurve.JZeroNeronPrimaryTorsionCore.exists_natCard_fppfCohomology_one_eq_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionCore_pow_nsmul_sections_eq_zero.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring

theorem ModularCurve.JZeroNeronPrimaryTorsionCore.pow_nsmul_sections_eq_zero
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (U : specInt.Fppf) (s : (C.𝒥 m).1.obj (Opposite.op U)) :
    q ^ m • s = 0 := by sorry
