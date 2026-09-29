-- Prove2me | Theorems.Thm_ModularCurve_jZeroNeronTorsionSheaf_h0_bounded_v5
-- name    : ModularCurve.jZeroNeronTorsionSheaf_h0_bounded_v5
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/c6626aa3-bd3f-5dc7-9b0f-d70e71057b90
-- title:
--   Boundedness of h⁰(m) for the primary Néron torsion sheaf
-- statement:
--   Let $p$ and $q$ be primes, let $A$ be a valuation subring of $\overline{\mathbb Q}$ with `A.LiesOverPrime p`, i.e. $p$ lies in the set of nonunits of $A$, and let $S$ be a term of `JZeroNeronPrimaryTorsionSheaf p q A hA`. Such a term consists of three layers: a core, which provides for every $m$ an abelian sheaf $\mathcal J_m$ on the small fppf site of $\operatorname{Spec}\mathbb Z$ whose sections over an fppf object $U$ are identified with the $\mathbb Z$-algebra homomorphisms from a flat finite-type Hopf algebra $H_m$ into $\Gamma(U,\mathcal O_U)$, functorially in $U$, together with identifications of the $\overline{\mathbb Q}$-points and the $A$-points of $H_m$ with `eisensteinPrimaryTorsionBar p q m` and `toricEisensteinPrimaryPart p q A hA m` compatibly with the group laws, the Galois action and the inclusion $A \subseteq \overline{\mathbb Q}$, short exact sequences $0 \to \mathcal J_m \to \mathcal J_{m+1} \to Q_m \to 0$, finite flat models at primes $\ell \neq p$ and fppf Kummer rows; a layer of finite flat models over the localisations and over $\mathbb Z/q$; and a layer of pinned numerical invariants $\mathrm{inv}(m)$ in `AdmissibleInvariants q` whose component $h^0(m)$ satisfies $\#H^0_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z,\mathcal J_m) = q^{h^0(m)}$. The conclusion is that there exists a natural number $H_0$ with $h^0(m) \le H_0$ for all $m$.
--
--   This is the uniform bound on the order of the group of integral points of the finite flat group schemes $\mathcal J_m$, in the shape required as a numerical input for the admissible-chain estimates: the integral points inject into the torsion of the group of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$-fixed points of `JZero p`, which is finite and does not depend on $m$. It is used by the two constructions of bounded admissible Kummer chains for the Hecke module of $J_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_jZeroNeronTorsionSheaf_h0_bounded_v5.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve AlgebraicGeometry AlgebraicGeometry.Scheme

theorem ModularCurve.jZeroNeronTorsionSheaf_h0_bounded_v5 (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p) (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (S : JZeroNeronPrimaryTorsionSheaf p q A hA) :
    ∃ H₀ : ℕ, ∀ m : ℕ, (S.invPins.inv m).h0 ≤ H₀ := by sorry
