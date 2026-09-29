-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionSheaf_prop17_of_forall_nonempty_jZeroNeronPrimaryTorsionFlag_two
-- name    : ModularCurve.JZeroNeronPrimaryTorsionSheaf.prop17_of_forall_nonempty_jZeroNeronPrimaryTorsionFlag_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/da276d65-7622-5df8-9cbc-71b73ef5ef5c
-- title:
--   Mazur's Proposition I.1.7 at the prime 2
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$, in the sense that $p$ is a non-unit of $A$. Let $S$ be a $2$-primary Néron torsion sheaf package for $p$ and $A$: its `core` provides fppf sheaves $\mathcal J_m$ on the small fppf site of $\operatorname{Spec}\mathbb Z$ together with flat finite-type $\mathbb Z$-Hopf algebras $H_m =$ `S.core.H m` whose points compute the sections of $\mathcal J_m$, identifications of the $\overline{\mathbb Q}$- and $A$-points with the $2$-primary Eisenstein torsion subgroup `eisensteinPrimaryTorsionBar p 2 m` of $J_0(p)$ and its toric part, and the short exact sequences $0 \to \mathcal J_m \to \mathcal J_{m+1} \to Q_m \to 0$; its `ffModels` provide fibre-by-fibre finite flat models; and its `invPins` attaches to each $m$ admissible invariants $(h^0,h^1,\delta,\alpha)$ at $q=2$, pinned by $\#H^0_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z,\mathcal J_m)=2^{h^0}$, $\#H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z,\mathcal J_m)=2^{h^1}$, $\#\,$`eisensteinPrimaryTorsionBar p 2 m`$=2^{\delta}\cdot\#\,$`toricEisensteinPrimaryPart p 2 A hA m`, and $\#$ of the $\overline{\mathbb F}_2$-points of the reduced finite flat model $=2^{\alpha}$. Assume further that for every $m$ the structure `JZeroNeronPrimaryTorsionFlag p 2 A hA S.core m` is inhabited, i.e. $\mathcal J_m$ carries a flag $F_0 \hookrightarrow \cdots \hookrightarrow F_n = \mathcal J_m$ of subsheaves represented by flat finite-type Hopf quotients $G_i$ of $H_m$, whose generic steps form a monotone chain of Galois-stable subgroups of $J_0(p)$ from $\bot$ to `eisensteinPrimaryTorsionBar p 2 m`, with $G_0$ having at most one $\overline{\mathbb Q}$-point and the last inclusion an isomorphism. The conclusion is that for every $m$ there is a natural number $a$ with $\#\operatorname{Hom}_{\mathbb Z\text{-alg}}(H_m, \overline{\mathbb F}_2) = 2^{a}$ and $h^1(m) + a \le h^0(m) + \delta(m)$ as integers.
--
--   This is the $q = 2$ form of Mazur's Proposition I.1.7 on the Eisenstein-primary torsion of $J_0(p)$, with the exponent $a$ counted on the $\overline{\mathbb F}_2$-points of the global Hopf algebra $H_m$ rather than read off from the pinned invariant $\alpha$. It feeds the construction of bounded admissible chains for the Hecke module $J_0(p)$ at the prime $2$, through [`ModularCurve.exists_jKummerRow_admissibleChain_bounded_heckeModuleBar_two_v5`](thm.html#ModularCurve.exists_jKummerRow_admissibleChain_bounded_heckeModuleBar_two_v5).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionSheaf_prop17_of_forall_nonempty_jZeroNeronPrimaryTorsionFlag_two.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring

theorem ModularCurve.JZeroNeronPrimaryTorsionSheaf.prop17_of_forall_nonempty_jZeroNeronPrimaryTorsionFlag_two (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (S : JZeroNeronPrimaryTorsionSheaf p 2 A hA)
    (hflag : ∀ m, Nonempty (JZeroNeronPrimaryTorsionFlag p 2 A hA S.core m)) :
    ∀ m : ℕ, ∃ a : ℕ,
      Nat.card (S.core.H m →ₐ[ℤ] AlgebraicClosure (ZMod 2)) = 2 ^ a ∧
      ((S.invPins.inv m).h1 : ℤ) + (a : ℤ) ≤ ((S.invPins.inv m).h0 : ℤ) + ((S.invPins.inv m).δ : ℤ) := by sorry
