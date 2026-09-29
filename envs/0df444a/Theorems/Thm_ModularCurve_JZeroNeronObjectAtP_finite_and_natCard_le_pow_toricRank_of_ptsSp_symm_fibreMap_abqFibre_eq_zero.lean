-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero
-- name    : ModularCurve.JZeroNeronObjectAtP.finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/52306fec-f610-5dca-af90-6b0d64f34bb1
-- title:
--   Counting extendable m-torsion points with trivial abelian-quotient reduction
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$ and $p$ prime, and suppose $p \nmid N_0$. Let $A$ be a valuation subring of an algebraic closure of $\mathbf{Q}$ lying over $p$, in the sense that $p$ is a nonunit of $A$, let $\Lambda$ be level data `JZeroNeronObjectAtP.LevelData N₀ p A` (a structure morphism $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec} \mathbf{Z}_{(p)}$ compatible with the generic point, a scheme $X$ over that base carrying a relative group law, and bijections $\Lambda.\mathrm{pts}$, $\Lambda.\mathrm{ptsSp}$ between $J_0(N_0)$ over $\bar{\mathbf{Q}}$, respectively over the residue field of $A$, and the corresponding sets of sections), with $\Lambda$ satisfying the predicate `IsJacobian`. Let $O$ be a `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`, with structure morphism $O.g \colon G \to \operatorname{Spec} \mathbf{Z}_{(p)}$, relative group law $O.L$, parametrisation $O.\mathrm{pts}$ of $J_0(N_0p)(\bar{\mathbf{Q}})$ by sections over the generic point, and toric rank $O.\mathrm{toricRank}$, and let $m > 0$. Consider the set of $x$ in $J_0(N_0p)$ (the degree-zero divisor class group of the level-$N_0p$ modular function field over $\bar{\mathbf{Q}}$) such that: $x$ is killed by $m$; there is a section $s$ of $O.g$ over $\sigma_A$, i.e. a morphism $\operatorname{Spec} A \to G$ with $s$ followed by $O.g$ equal to $\sigma_A$, whose restriction along $\mathrm{barPt}\,A$ is the point $(O.\mathrm{pts}\,x).1$, and such that for $i = 0, 1$ the element $\Lambda.\mathrm{ptsSp}^{-1}$ of the image, under the morphism `O.abqFibre i` of base changes along $\mathrm{resPt}\,A$ followed by $\sigma_A$ from that of $O.g$ to that of $\Lambda.f$, of the reduction $\mathrm{resPt}\,A$ followed by $s$ vanishes; and $(\mathrm{degeneracyPushforwardPair}\ N_0\ p\ i)(x) = 0$ for $i = 0, 1$, where this pair of additive maps $J_0(N_0p) \to J_0(N_0)$ is the pair of pushforwards along the two degeneracy inclusions $\alpha, \beta$ when the integrality, finiteness and norm-formula inputs `DegeneracyPushforwardInputs` hold, and is zero otherwise. The assertion is that this set is finite and that its cardinality is at most $m^{O.\mathrm{toricRank}}$.
--
--   This is the upper bound in the comparison of the $m$-torsion of the toric part of the special fibre at $p$ with the group of $m$-torsion classes that extend over $A$, lie in the joint kernel of the two degeneracy pushforwards, and reduce with vanishing abelian-quotient coordinates; it rests on Grothendieck's toric/abelian analysis of the special fibre together with a count of sections over a henselian valuation ring. It is used in [`ModularCurve.JZeroNeronObjectAtP.ptsSp_symm_fibreMap_abqFibre_ne_zero_of_mem_finPts_of_not_mem_toricPts`](thm.html#ModularCurve.JZeroNeronObjectAtP.ptsSp_symm_fibreMap_abqFibre_ne_zero_of_mem_finPts_of_not_mem_toricPts) to show that a point outside the toric part has nonzero abelian-quotient reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP
open AlgebraicGeometry

theorem ModularCurve.JZeroNeronObjectAtP.finite_and_natCard_le_pow_toricRank_of_ptsSp_symm_fibreMap_abqFibre_eq_zero
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) :
    {x : JZero (N₀ * p) | x ∈ jZeroTorsion (N₀ * p) m ∧
      (∃ s : SchemeHomOver Λ.σA O.g, (O.pts x).1 = barPt A ≫ s.1 ∧
        Λ.ptsSp.symm (fibreMap (O.abqFibre 0) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) = 0 ∧
        Λ.ptsSp.symm (fibreMap (O.abqFibre 1) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) = 0) ∧
      degeneracyPushforwardPair N₀ p 0 x = 0 ∧ degeneracyPushforwardPair N₀ p 1 x = 0}.Finite ∧
    Nat.card {x : JZero (N₀ * p) | x ∈ jZeroTorsion (N₀ * p) m ∧
      (∃ s : SchemeHomOver Λ.σA O.g, (O.pts x).1 = barPt A ≫ s.1 ∧
        Λ.ptsSp.symm (fibreMap (O.abqFibre 0) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) = 0 ∧
        Λ.ptsSp.symm (fibreMap (O.abqFibre 1) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) = 0) ∧
      degeneracyPushforwardPair N₀ p 0 x = 0 ∧ degeneracyPushforwardPair N₀ p 1 x = 0} ≤ m ^ O.toricRank := by sorry
