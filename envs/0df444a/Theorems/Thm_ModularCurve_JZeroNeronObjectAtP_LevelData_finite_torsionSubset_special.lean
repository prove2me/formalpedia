-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelData_finite_torsionSubset_special
-- name    : ModularCurve.JZeroNeronObjectAtP.LevelData.finite_torsionSubset_special
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/d9f5d04a-8898-5b43-ae21-16e591cc93eb
-- title:
--   Finiteness of n-torsion in the special fibre of J₀(N₀)
-- statement:
--   Fix a natural number $N_0 \neq 0$ and a prime $p$ with $p \nmid N_0$, and let $A$ be a valuation subring of $\overline{\mathbf Q}$ satisfying `LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbf Q}$ is a nonunit of $A$. Let $\Lambda$ be a datum of type `LevelData N₀ p A`: a morphism $\sigma_A \colon \operatorname{Spec} A \to$ `base p` whose composite with `barPt A` is `genPt p`, a scheme $X$ with a structure morphism $f \colon X \to$ `base p`, a relative group law $L$ on $f$ over `baseRing p` (fibrewise functorial multiplication, unit and inverse on sections of $f$), together with bijections `pts` from `JZero N₀` onto the sections of $f$ over `genPt p` and `ptsSp` from `JZeroC (ResidueField A) N₀` onto the sections of $f$ over the special point $\operatorname{Spec}$ of the residue field of $A$ mapping to `base p` through $\sigma_A$. Assume $\Lambda$ satisfies `IsJacobian`: the abelian-scheme property bundle for $f$, commutativity of $L$, additivity of `pts` and of `ptsSp`, Galois equivariance of `pts`, compatibility of reduction of points modulo the maximal ideal when the inputs `ReductionInputsModL` hold, and realisation of each Hecke operator by an endomorphism of $f$ compatible with $L$. Then for every $n > 0$ the set of sections $x$ of $\Lambda.f$ over the composite `resPt A ≫ Λ.σA` with $n \cdot x$ equal to the unit section is finite.
--
--   This is the finiteness of the $n$-torsion of the group of points of the special fibre at a place above $p$ of the Jacobian datum attached to $X_0(N_0)$, valid for all $n \ge 1$ including those divisible by $p$; classically it is the finiteness of $\operatorname{Pic}^0[n]$ for a curve over an algebraically closed field of characteristic $p$. It feeds the local quasi-finiteness of multiplication by $n$ on fibres used in [`ModularCurve.DRModelPackageLevel.locallyQuasiFinite_fibre_schemeNsmul_of_not_isUnit`](thm.html#ModularCurve.DRModelPackageLevel.locallyQuasiFinite_fibre_schemeNsmul_of_not_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_LevelData_finite_torsionSubset_special.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.LevelData.finite_torsionSubset_special
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian) (n : ℕ) (hn : 0 < n) :
    (Λ.L.torsionSubset (resPt A ≫ Λ.σA) n).Finite := by sorry
