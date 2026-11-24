-- Prove2me | Theorems.Thm_IsLocalRing_exists_approximable_henselization_of_localization_atPrime
-- name    : IsLocalRing.exists_approximable_henselization_of_localization_atPrime
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T19:57:38.169248+00:00
-- url     : https://prove2.me/theorems/53253b35-fe7c-4750-bcdc-4be170d5bbce
-- title:
--   Artin approximation after henselization of an essentially finite type local ring
-- statement:
--   Let $D$ be a finite type $\mathbf Z$-algebra, $S=D_{\mathfrak p}$, and $S\to A$ a local map into a henselian local ring. There is a factorization through a Noetherian henselian local ring $R$ with local structure maps such that any finite polynomial system over $R$ with a solution in its completion has a solution over $R$ with the same reduction in the residue field of the completion.
-- source:
--   Take the henselization of S and apply Stacks Project, Proposition 15.51.12, Lemma 15.51.8 and Theorem 16.13.1 (https://stacks.math.columbia.edu/tag/07QY).

import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Henselian

set_option autoImplicit false
universe u

theorem IsLocalRing.exists_approximable_henselization_of_localization_atPrime
    (D S A : Type u) [CommRing D] [CommRing S] [CommRing A] [Algebra ℤ D]
    [Algebra.FiniteType ℤ D] (p : Ideal D) [p.IsPrime] [Algebra D S]
    [IsLocalization p.primeCompl S] [IsLocalRing S] [HenselianLocalRing A]
    (f : S →+* A) [IsLocalHom f] :
    ∃ (R : Type u) (_ : CommRing R) (_ : HenselianLocalRing R) (_ : IsNoetherianRing R)
      (a : R →+* A) (_ : IsLocalHom a) (b : S →+* R) (_ : IsLocalHom b),
      a.comp b = f ∧
        let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
        ∀ (n m : ℕ) (P : Fin m → MvPolynomial (Fin n) R) (x' : Fin n → C),
          (∀ k, MvPolynomial.aeval x' (P k) = 0) →
          ∃ x : Fin n → R, (∀ k, MvPolynomial.aeval x (P k) = 0) ∧
            ∀ k, IsLocalRing.residue C (x' k) = IsLocalRing.ResidueField.map (algebraMap R C)
              (IsLocalRing.residue R (x k)) := by sorry
