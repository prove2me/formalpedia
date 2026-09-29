-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionCore_exists_natCard_fppfCohomology_one_eq_pow
-- name    : ModularCurve.JZeroNeronPrimaryTorsionCore.exists_natCard_fppfCohomology_one_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/fb793b13-c627-57fc-b456-a93ce8e67c1e
-- title:
--   Fppf H¹ of a Néron core sheaf has q-power order
-- statement:
--   Fix natural numbers $p$ and $q$, each assumed prime, and a valuation subring $A$ of $\overline{\mathbb Q}$ satisfying `A.LiesOverPrime p`, i.e. the image of $p$ lies in the set of nonunits of $A$. Let $C$ be an element of the structure `JZeroNeronPrimaryTorsionCore p q A hA`, whose data comprise: a family $\mathcal J_m = C.\mathcal J\,m$ of sheaves of abelian groups on the small fppf site of $\operatorname{Spec}\mathbb Z$ (the site of objects over $\operatorname{Spec}\mathbb Z$ with the fppf morphism property, with its small Grothendieck topology); a family of commutative rings $H_m$ carrying $\mathbb Z$-Hopf algebra, finite-type and flatness structures; additive identifications of the sections of $\mathcal J_m$ over any $U$ with the group $\mathrm{WithConv}(H_m \to_{\mathbb Z\text{-alg}} \Gamma(U_{\text{left}},\top))$ under convolution, natural in $U$; bijections of $\mathrm{WithConv}(H_m \to_{\mathbb Z\text{-alg}} \overline{\mathbb Q})$, respectively $\mathrm{WithConv}(H_m \to_{\mathbb Z\text{-alg}} A)$, with the subgroup `eisensteinPrimaryTorsionBar p q m` of $q^m$-torsion points of $\mathrm{JZero}\,p$ lying in the union of the torsion submodules for powers of the Eisenstein maximal ideal, respectively with its intersection `toricEisensteinPrimaryPart` with the toric part, compatibly with convolution, with the Galois action and with each other; finiteness of $H_m$ after localisation away from $p$; short exact sequences $0 \to \mathcal J_m \to \mathcal J_{m+1} \to \mathcal Q_m \to 0$; and Kummer-row data. For every $m$ there exists $n \in \mathbb N$ with $\#H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z, \mathcal J_m) = q^n$, the cardinality being `Nat.card` of the first fppf sheaf cohomology group; since $q$ is prime the right-hand side is positive, so the assertion includes finiteness of this cohomology group.
--
--   This is the finiteness-and-$q$-power-order statement for the first fppf cohomology of the $\mathfrak P$-primary $q^m$-torsion sheaf of the Néron model of $J_0(p)$ over $\operatorname{Spec}\mathbb Z$, in the style of Mazur's invariant $h^1$ for quasi-finite flat group schemes over $\operatorname{Spec}\mathbb Z$. It feeds the construction of the associated pinning data, via [`ModularCurve.nonempty_jZeroNeronPrimaryTorsionInvPins`](thm.html#ModularCurve.nonempty_jZeroNeronPrimaryTorsionInvPins).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionCore_exists_natCard_fppfCohomology_one_eq_pow.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring

theorem ModularCurve.JZeroNeronPrimaryTorsionCore.exists_natCard_fppfCohomology_one_eq_pow
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ) :
    ∃ n : ℕ, Nat.card (fppfCohomology specInt (C.𝒥 m) 1) = q ^ n := by sorry
