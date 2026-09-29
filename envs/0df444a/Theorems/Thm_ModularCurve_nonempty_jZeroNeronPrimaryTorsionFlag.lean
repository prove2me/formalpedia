-- Prove2me | Theorems.Thm_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFlag
-- name    : ModularCurve.nonempty_jZeroNeronPrimaryTorsionFlag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/ea6b9e17-f791-54b9-8180-881c79ba2b01
-- title:
--   Existence of a flag for the Eisenstein-primary torsion sheaf
-- statement:
--   Let $p$ and $q$ be primes, let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ (the predicate `LiesOverPrime`, i.e. $(p:\overline{\mathbb Q})\in A.\mathrm{nonunits}$), let $C$ be a `JZeroNeronPrimaryTorsionCore` for $p$, $q$, $A$, and let $m$ be a natural number. The assertion is that the type `JZeroNeronPrimaryTorsionFlag p q A hA C m` is nonempty: there exist $n$, a family $G_0,\dots,G_n$ of commutative rings that are flat finite-type Hopf algebras over $\mathbb Z$, surjective $\mathbb Z$-algebra maps $\pi_i\colon C.H\,m\to G_i$ and surjective $\mathbb Z$-algebra maps $G_{i+1}\to G_i$ compatible with the $\pi_i$; a family $F_0,\dots,F_n$ of abelian-group sheaves on the small fppf site of $\operatorname{Spec}\mathbb Z$ together with monomorphisms $\iota_i\colon F_i\to C.\mathcal J\,m$ and maps $F_i\to F_{i+1}$ over $C.\mathcal J\,m$, where the sections of $F_i$ on $U$ are identified additively with the convolution group of $\mathbb Z$-algebra maps $G_i\to\Gamma(U,\top)$ compatibly with $\iota_i$ and $\pi_i$; $G_0$ admits at most one $\mathbb Z$-algebra map to $\overline{\mathbb Q}$ and $\iota_n$ is an isomorphism; and a monotone, Galois-stable chain of additive subgroups $\mathrm{genericStep}_i$ of $JZero\,p=\operatorname{Pic}^0$ of the level-$p$ modular function field over $\overline{\mathbb Q}$, running from $\bot$ to `eisensteinPrimaryTorsionBar p q m` (the $q^m$-torsion intersected with the union of the Eisenstein-maximal-ideal-power torsion submodules); together with the remaining fields of `JZeroNeronPrimaryTorsionFlag`, summarised here.
--
--   This is the formal counterpart of Mazur's dévissage of the Eisenstein-primary $q^m$-torsion of $J_0(p)$ into layers of order $q$, realised simultaneously as a filtration of the associated fppf sheaf by flat Hopf-algebra quotients. It feeds the finiteness statements for the first fppf cohomology of a Néron core, [`ModularCurve.finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore`](thm.html#ModularCurve.finite_fppfCohomology_one_jZeroNeronPrimaryTorsionCore) and its variant for $q\neq 2$, and the construction of bounded admissible chains used with the Kummer rows.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFlag.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring

theorem ModularCurve.nonempty_jZeroNeronPrimaryTorsionFlag (p : ℕ) [Fact p.Prime]
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ) :
    Nonempty (JZeroNeronPrimaryTorsionFlag p q A hA C m) := by sorry
