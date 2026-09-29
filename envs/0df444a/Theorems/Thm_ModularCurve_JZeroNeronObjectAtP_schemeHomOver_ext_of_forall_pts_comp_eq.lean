-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_schemeHomOver_ext_of_forall_pts_comp_eq
-- name    : ModularCurve.JZeroNeronObjectAtP.schemeHomOver_ext_of_forall_pts_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/cd07aa8e-47bf-5180-bb91-234cdf936de5
-- title:
--   Rigidity: morphisms out of G are determined on ℚ̄-points
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0$ nonzero and $p$ prime, and assume $p \nmid N_0$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that $p$, viewed in $\overline{\mathbb{Q}}$, is a non-unit of $A$. Let $\Lambda$ be a level datum of type `LevelData N₀ p A`: it provides a morphism $\sigma_A : \operatorname{Spec} A \to$ `base p` compatible with the generic point, a scheme $X$ with a structure morphism $f : X \to$ `base p`, a relative group law on $f$ over the ring `baseRing p`, and bijections identifying $J_0(N_0)$-type class groups — the degree-zero divisor class group `JZero N₀` of the modular function field at level $N_0$ over $\overline{\mathbb{Q}}$, and its analogue over the residue field of $A$ — with the sections of $f$ over the geometric generic point and over $\operatorname{Spec}$ of the residue field respectively. Assume $\Lambda$ satisfies `IsJacobian`, the conjunction of: $f$ carries an abelian-scheme property bundle over `baseRing p`, the group law is commutative, both point bijections are additive, the generic bijection is Galois-equivariant, reduction of points is compatible modulo $\ell$ when the relevant inputs exist, and every Hecke operator is realised by an endomorphism of $f$ over the base. Let $O$ be a `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`, i.e. a scheme $G$ with $g : G \to$ `base p`, a relative group law with the listed geometric properties (smooth, separated, locally of finite type, quasi-compact, surjective, with preconnected fibres, flat and surjective multiplication by each positive integer, proper generic fibre, and further numerical and Hecke data summarised here), together with a bijection `O.pts` from `JZero (N₀ * p)` onto the sections of $g$ over the geometric generic point, additive, Galois-equivariant and Hecke-compatible. Finally let $\psi_1, \psi_2$ be two morphisms $G \to X$ over `base p` (that is, elements of `SchemeHomOver O.g Λ.f`: morphisms whose composite with $f$ is $g$) such that for every $x \in$ `JZero (N₀ * p)` the point `(O.pts x).1` followed by $\psi_1$ equals the same point followed by $\psi_2$. Then $\psi_1 = \psi_2$.
--
--   This is the rigidity (schematic density of the generic fibre) step in the comparison of level-$N_0p$ and level-$N_0$ models: a morphism from the smooth base scheme $G$ to $X$ over $\mathbb{Z}_{(p)}$ is determined by its effect on the geometric generic points coming from the degree-zero class group. It is used to identify Hecke- and degeneracy-type morphisms, and is cited in the construction of nontrivial Hecke torsion from the special-fibre point dictionary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_schemeHomOver_ext_of_forall_pts_comp_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.schemeHomOver_ext_of_forall_pts_comp_eq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (ψ₁ ψ₂ : SchemeHomOver O.g Λ.f)
    (h : ∀ x : JZero (N₀ * p), (O.pts x).1 ≫ ψ₁.1 = (O.pts x).1 ≫ ψ₂.1) :
    ψ₁ = ψ₂ := by sorry
