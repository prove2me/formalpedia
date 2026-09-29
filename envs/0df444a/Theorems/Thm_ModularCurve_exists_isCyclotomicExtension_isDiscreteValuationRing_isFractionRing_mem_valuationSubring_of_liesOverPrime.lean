-- Prove2me | Theorems.Thm_ModularCurve_exists_isCyclotomicExtension_isDiscreteValuationRing_isFractionRing_mem_valuationSubring_of_liesOverPrime
-- name    : ModularCurve.exists_isCyclotomicExtension_isDiscreteValuationRing_isFractionRing_mem_valuationSubring_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/94fee069-dbb0-571a-a375-fcf886314d9a
-- title:
--   A cyclotomic DVR inside a place above p
-- statement:
--   Let $p$ be a prime and let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `P.LiesOverPrime p`, which by definition means that the image of $p$ in $\overline{\mathbb{Q}}$ lies in `P.nonunits`, i.e. $p$ belongs to $P$ and is not a unit there. The assertion is the existence of: a field $L$ (in `Type`) of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, an element $\zeta \in L$ that is a primitive $p$-th root of unity, and a commutative ring $A$ which is a domain and a discrete valuation ring, together with an algebra structure $A \to L$ making $L$ a fraction field of $A$, such that the image of $p$ in $A$ lies in the maximal ideal $\mathfrak m_A$ of the local ring $A$ and $\zeta$ lies in the image of $A \to L$; furthermore algebra structures $A \to \overline{\mathbb{Q}}$ and $L \to \overline{\mathbb{Q}}$ forming a scalar tower $A \to L \to \overline{\mathbb{Q}}$, for which the two stated conditions hold: every element of $A$ maps into the valuation subring $P$, and an element $a \in A$ lies in $\mathfrak m_A$ if and only if the $P$-valuation of its image in $\overline{\mathbb{Q}}$ is $< 1$.
--
--   This packages the standard local cyclotomic data at a place of $\overline{\mathbb{Q}}$ above $p$: the field $\mathbb{Q}(\zeta_p)$ together with the localisation of its ring of integers at the prime induced by $P$, embedded compatibly in $\overline{\mathbb{Q}}$ so that the maximal ideal of the discrete valuation ring is cut out by $P$. It supplies the base-ring binders for the $q$-expansion/semistable specialisation statement that cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isCyclotomicExtension_isDiscreteValuationRing_isFractionRing_mem_valuationSubring_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.exists_isCyclotomicExtension_isDiscreteValuationRing_isFractionRing_mem_valuationSubring_of_liesOverPrime (p : ℕ) [Fact p.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ (L : Type) (_ : Field L) (_ : CharZero L) (_ : IsCyclotomicExtension {p} ℚ L) (ζ : L) (_ : IsPrimitiveRoot ζ p)
      (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (_ : Algebra A L) (_ : IsFractionRing A L)
      (_ : (p : A) ∈ IsLocalRing.maximalIdeal A) (_ : ∃ z : A, algebraMap A L z = ζ)
      (_ : Algebra A (AlgebraicClosure ℚ)) (_ : Algebra L (AlgebraicClosure ℚ)) (_ : IsScalarTower A L (AlgebraicClosure ℚ)),
      (∀ a : A, algebraMap A (AlgebraicClosure ℚ) a ∈ P) ∧
      (∀ a : A, a ∈ IsLocalRing.maximalIdeal A ↔ P.valuation (algebraMap A (AlgebraicClosure ℚ) a) < 1) := by sorry
