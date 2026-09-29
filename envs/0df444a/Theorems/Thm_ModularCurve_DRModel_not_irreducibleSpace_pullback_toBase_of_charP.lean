-- Prove2me | Theorems.Thm_ModularCurve_DRModel_not_irreducibleSpace_pullback_toBase_of_charP
-- name    : ModularCurve.DRModel.not_irreducibleSpace_pullback_toBase_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/1e2d9bd5-987c-5c90-9425-0076bb7762fc
-- title:
--   Characteristic-p fibres of the Deligne–Rapoport model are reducible
-- statement:
--   Let $p$ be a prime and let $k$ be a field of characteristic $p$. Write $F = \mathrm{modularFunctionFieldFull}\,p$, the subfield of the Laurent series field $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions at level $p$, and let $j = \mathrm{IgusaScheme.jFull}\,p \in F$ be the element given by the $q$-expansion of the modular invariant. The scheme $\mathrm{DRModel}\,p$ is the two-chart integral model $\mathrm{TwoChartIntegralModel}\,\mathbb{Z}\,F\,j$, namely the pushout of the two gluing maps attached to the subalgebras $\mathrm{chartAlgFin} = \mathrm{chartAlg}\,\mathbb{Z}\,F\,\{j\}$ and $\mathrm{chartAlgInf} = \mathrm{chartAlg}\,\mathbb{Z}\,F\,\{j^{-1}\}$ of $F$, and $\mathrm{DRModel.toBase}\,p : \mathrm{DRModel}\,p \to \operatorname{Spec}\mathbb{Z}$ is the morphism obtained from the two structure morphisms $\operatorname{Spec}(\mathrm{chartAlgFin}) \to \operatorname{Spec}\mathbb{Z}$ and $\operatorname{Spec}(\mathrm{chartAlgInf}) \to \operatorname{Spec}\mathbb{Z}$ by the universal property of the pushout. The assertion is that the underlying topological space of the fibre product of $\mathrm{DRModel.toBase}\,p$ with $\operatorname{Spec}$ of the canonical ring map $\mathbb{Z} \to k$ is not an irreducible space, i.e. it is not both nonempty and such that any two nonempty open subsets meet.
--
--   This is the reducibility of the characteristic-$p$ fibre of the Deligne–Rapoport model of $X_0(p)$, whose special fibre classically consists of two rational components meeting at the supersingular points; the statement is formulated for an arbitrary field of characteristic $p$, both components being already defined over $\mathbb{F}_p$. It is used to separate the two components of the special fibre, for instance to show that the generic points of the images of the two charts in the base-changed model differ and to produce the two residue fields of those generic points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModel_not_irreducibleSpace_pullback_toBase_of_charP.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModel.not_irreducibleSpace_pullback_toBase_of_charP
    (p : ℕ) [Fact p.Prime] [NeZero p] (k : Type) [Field k] [CharP k p] :
    ¬ IrreducibleSpace ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := by sorry
