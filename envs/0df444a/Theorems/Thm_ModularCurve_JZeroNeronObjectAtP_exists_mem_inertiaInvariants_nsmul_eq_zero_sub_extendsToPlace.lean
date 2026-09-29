-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_mem_inertiaInvariants_nsmul_eq_zero_sub_extendsToPlace
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_mem_inertiaInvariants_nsmul_eq_zero_sub_extendsToPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/89b3cf64-3923-5014-84ee-349546e4f1a0
-- title:
--   Prime-to-p division modulo points extending to the place
-- statement:
--   Fix natural numbers $N_0 \neq 0$ and $p$ with $p$ prime and $p \nmid N_0$, a valuation subring $A$ of a fixed algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ with $p$ a non-unit of $A$, a level datum $\Lambda$ of type `LevelData N₀ p A` (a structure morphism $\sigma_A : \operatorname{Spec} A \to$ `base p` whose composite with `barPt A` is the generic point `genPt p`, a scheme $X$ over `base p` with a relative group law and bijections identifying $J_0(N_0)$-classes and their specialisations with sections), a hypothesis $h\Lambda$ asserting the conjunction `Λ.IsJacobian` (abelian-scheme properties of $\Lambda.f$, commutativity of the group law, additivity and Galois-equivariance of `Λ.pts`, additivity of `Λ.ptsSp`, compatibility of reduction of points, and realisation of the Hecke operators by endomorphisms), and an object $O$ of type `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`, consisting of a scheme $G$ with a smooth, separated, surjective, quasi-compact morphism $g$ of locally finite type to `base p` with connected fibres, a commutative relative group law $L$, a bijection `O.pts` from $\mathrm{Pic}^0$ of the level-$N_0p$ modular function field over $\overline{\mathbb Q}$, written `JZero (N₀ * p)`, onto the sections of $g$ over `genPt p`, additive and Galois-equivariant, together with Hecke endomorphisms, flatness and surjectivity of multiplication by every positive integer, properness of the generic fibre, and further data. Let $m > 0$ be coprime to $p$, and let $y \in$ `JZero (N₀ * p)` be fixed by the inertia subgroup of $A$ in $\mathbb{Q}$, and suppose that the section $O.\mathrm{pts}(m \cdot y)$ over `genPt p` extends to the place, that is, equals `barPt A` followed by some section of $g$ over $\sigma_A$. Then there exists $x \in$ `JZero (N₀ * p)`, also fixed by the inertia subgroup of $A$, with $m \cdot x = 0$ and such that the section $O.\mathrm{pts}(y - x)$ likewise factors as `barPt A` followed by a section of $g$ over $\sigma_A$.
--
--   This is the prime-to-$p$ divisibility statement for the identity component of the Néron model at $p$, phrased entirely in terms of sections of $g$ rather than of the component group: multiplication by $m$ is surjective on $A$-points, so an inertia-invariant class whose $m$-th multiple extends to $A$ differs from an extending class by an inertia-invariant $m$-torsion class. It is used in the assembly of the ordinary Néron data at $p$ from the data attached to the constituent levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_mem_inertiaInvariants_nsmul_eq_zero_sub_extendsToPlace.lean

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

theorem ModularCurve.JZeroNeronObjectAtP.exists_mem_inertiaInvariants_nsmul_eq_zero_sub_extendsToPlace
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) (hmp : m.Coprime p)
    (y : JZero (N₀ * p)) (hy : y ∈ inertiaInvariants A (N₀ * p))
    (hmy : ExtendsToPlace A Λ.σA (O.pts (m • y))) :
    ∃ x : JZero (N₀ * p), x ∈ inertiaInvariants A (N₀ * p) ∧ m • x = 0 ∧
      ExtendsToPlace A Λ.σA (O.pts (y - x)) := by sorry
