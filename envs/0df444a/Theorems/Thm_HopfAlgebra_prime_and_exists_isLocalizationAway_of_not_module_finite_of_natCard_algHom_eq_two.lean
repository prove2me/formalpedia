-- Prove2me | Theorems.Thm_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two
-- name    : HopfAlgebra.prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/05d45e65-2a8b-5b46-a7b6-d5b284b71215
-- title:
--   Non-finite order-two Hopf algebras over ℤ
-- statement:
--   Let $p$ be a natural number and let $K$ be a commutative ring carrying a Hopf algebra structure over $\mathbf Z$ which is of finite type and flat as a $\mathbf Z$-algebra, respectively $\mathbf Z$-module. Assume that for every prime $\ell \neq p$ the base change $R_\ell \otimes_{\mathbf Z} K$ is a finite module over $R_\ell$, where $R_\ell \subseteq \mathbf Q$ is the subring of rationals whose denominator is coprime to $\ell$; that the number of $\mathbf Z$-algebra homomorphisms $K \to \overline{\mathbf Q}$ is exactly $2$; and that $K$ is not a finite $\mathbf Z$-module. Then $p$ is prime, and there exist a commutative ring $K_0$ with a Hopf algebra structure over $\mathbf Z$, a homomorphism $\psi : K_0 \to K$ of $\mathbf Z$-bialgebras and an element $f \in K_0$ such that, for the $K_0$-algebra structure on $K$ given by $\psi$, $K$ is the localisation of $K_0$ away from $f$, and one of the following holds: either there is an isomorphism of $\mathbf Z$-algebras $e : K_0 \to \mathbf Z^{2}$ (functions on `Fin 2`) with $e(f) = (1, p)$ and with the counit of $K_0$ equal to the first coordinate of $e$; or $p \neq 2$ and there is an isomorphism of $\mathbf Z$-bialgebras $e : K_0 \to \mathbf Z[\mathbf Z/2]$ onto the monoid algebra of the multiplicative group of order two, with $e(f)$ the element $\tfrac{p+1}{2}\cdot 1 + \tfrac{1-p}{2}\cdot g$, the coefficients being the integer quotients by $2$ and $g$ the nontrivial group element.
--
--   This is Mazur's classification of the order-two quasi-finite flat commutative group schemes over $\operatorname{Spec}\mathbf Z$ which are finite away from a single prime $p$ but not finite: such a scheme is the extension by zero across the fibre at $p$ of either the constant group $\mathbf Z/2$ or, for odd $p$, of $\mu_2$ over $\mathbf Z[1/p]$, the element $f$ cutting out the open complement of that fibre. It feeds the analysis of order-two subgroup schemes in the study of the modular curve, being cited by [`ModularCurve.exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two`](thm.html#ModularCurve.exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two.lean

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.Fin.VecNotation
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two
    (p : ℕ) (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgen : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 2)
    (hK : ¬ Module.Finite ℤ K) :
    p.Prime ∧
    ∃ (K₀ : Type) (_ : CommRing K₀) (_ : HopfAlgebra ℤ K₀) (ψ : K₀ →ₐc[ℤ] K) (f : K₀),
      (letI : Algebra K₀ K := (ψ : K₀ →+* K).toAlgebra; IsLocalization.Away f K) ∧
      ((∃ e : K₀ ≃ₐ[ℤ] (Fin 2 → ℤ), e f = ![1, (p : ℤ)] ∧
          ∀ x : K₀, Bialgebra.counitAlgHom ℤ K₀ x = e x 0) ∨
       (p ≠ 2 ∧ ∃ e : K₀ ≃ₐc[ℤ] MonoidAlgebra ℤ (Multiplicative (ZMod 2)),
          e f = MonoidAlgebra.single 1 (((p : ℤ) + 1) / 2) +
            MonoidAlgebra.single (Multiplicative.ofAdd 1) ((1 - (p : ℤ)) / 2))) := by sorry
