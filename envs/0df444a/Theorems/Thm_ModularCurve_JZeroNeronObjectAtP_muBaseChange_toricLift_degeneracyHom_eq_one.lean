-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_muBaseChange_toricLift_degeneracyHom_eq_one
-- name    : ModularCurve.JZeroNeronObjectAtP.muBaseChange_toricLift_degeneracyHom_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/851c8122-f761-53ee-86e0-9b52b529b441
-- title:
--   Degeneracy maps kill the toric lift over the residue field
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$ and $p$ prime, and assume $p \nmid N_0$. Let $A$ be a valuation subring of a fixed algebraic closure of $\mathbb{Q}$ with $p$ lying in its non-units, i.e. in its maximal ideal, and write $\kappa =$ `ResidueField ↥A`. Let $\Lambda$ be level data of level $N_0$ at $p$ over $A$: a structure morphism $\sigma_A \colon \operatorname{Spec} A \to$ `base p` compatible with the generic point, a scheme $X$ with a morphism $f \colon X \to$ `base p`, a relative group law $\Lambda.L$ on $f$ over `baseRing p`, and bijections of $J_0(N_0)$ (respectively of its $\kappa$-points) with the sections of $f$ over the generic point (respectively over $\operatorname{resPt} A \circ \sigma_A$); assume $\Lambda$ satisfies `IsJacobian`, i.e. $f$ carries an abelian-scheme property bundle, $\Lambda.L$ is commutative, both point bijections are additive, the generic points are Galois-equivariant, reduction of points agrees modulo $\ell$ when the relevant inputs hold, and every Hecke operator is realised by an endomorphism of $f$ over `base p` compatible with $\Lambda.L$. Let $\mathcal{O}$ be a Néron object of level $N_0p$ at $p$ over $A$ above $\Lambda$, with group scheme $g \colon G \to$ `base p`, toric rank $t = \mathcal{O}.\mathrm{toricRank}$, toric lifts and degeneracy homomorphisms. Then for every $m > 0$ and every $i \in \{0,1\}$, the composite of the base-change morphism $\mu^t_{m,\kappa} \to \mu^t_{m,A}$ induced by the residue map of $A$, followed by the underlying morphism of $\mathcal{O}.\mathrm{toricLift}\,m$, the projection $\mathrm{pr}_1$ of the fibre product of $g$ and $\sigma_A$ onto $G$, and the underlying morphism of the $i$-th degeneracy homomorphism $\mathcal{O}.\mathrm{degeneracyHom}\,i \colon G \to X$, equals the underlying morphism of the unit section $\Lambda.L.\mathrm{one}$ over the base morphism $\mu^t_{m,\kappa} \to \operatorname{Spec}\kappa \to \operatorname{Spec} A \to$ `base p`.
--
--   This is the scheme-theoretic form of the statement that the toric part of the Néron model of $J_0(N_0p)$ at $p$ becomes trivial in $J_0(N_0)$ under either degeneracy map: a morphism from a group scheme of multiplicative type to an abelian scheme over the residue field is the unit section. It is the input to [`ModularCurve.JZeroNeronObjectAtP.muPt_toricLift_degeneracyHom_eq_one`](thm.html#ModularCurve.JZeroNeronObjectAtP.muPt_toricLift_degeneracyHom_eq_one), and thence to the analysis of the character group of the toric part used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_muBaseChange_toricLift_degeneracyHom_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
  ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.muBaseChange_toricLift_degeneracyHom_eq_one
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) (i : Fin 2) :
    muBaseChange (residue ↥A) O.toricRank m ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA ≫ (O.degeneracyHom i).1 =
      (Λ.L.one (muStr (ResidueField ↥A) O.toricRank m ≫ resPt A ≫ Λ.σA)).1 := by sorry
