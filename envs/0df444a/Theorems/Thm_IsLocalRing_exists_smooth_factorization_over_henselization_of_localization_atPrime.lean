-- Prove2me | Theorems.Thm_IsLocalRing_exists_smooth_factorization_over_henselization_of_localization_atPrime
-- name    : IsLocalRing.exists_smooth_factorization_over_henselization_of_localization_atPrime
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T20:39:51.688024+00:00
-- url     : https://prove2.me/theorems/c85f6658-1491-4cd2-a0ed-1f55631efb74
-- title:
--   Smooth factorization into the completion of an essentially finite type henselization
-- statement:
--   Let $D$ be a finite type $\mathbf Z$-algebra, $S=D_{\mathfrak p}$ and $R$ its Noetherian henselization, specified by the universal property for local maps into henselian local rings. Every $R$-algebra map from a finitely presented $R$-algebra $B$ to $\widehat R$ factors through a smooth $R$-algebra.
-- source:
--   Stacks Project, Proposition 15.51.12, Lemmas 15.51.7 and 15.51.8, and Theorem 16.12.1 (https://stacks.math.columbia.edu/tag/07GC).

import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RingHom.Smooth

set_option autoImplicit false
universe u

theorem IsLocalRing.exists_smooth_factorization_over_henselization_of_localization_atPrime
    (D S R : Type u) [CommRing D] [CommRing S] [CommRing R] [Algebra ℤ D]
    [Algebra.FiniteType ℤ D] (p : Ideal D) [p.IsPrime] [Algebra D S] [IsLocalization p.primeCompl S]
    [IsLocalRing S] [HenselianLocalRing R] [IsNoetherianRing R]
    (b : S →+* R) [IsLocalHom b]
    (_ : ∀ (A : Type u) [CommRing A] [HenselianLocalRing A] (f : S →+* A) [IsLocalHom f],
      ∃! a : R →+* A, IsLocalHom a ∧ a.comp b = f)
    (B : Type u) [CommRing B] [Algebra R B] [Algebra.FinitePresentation R B]
    (g : B →ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal R) R) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E) (_ : Algebra.Smooth R E)
      (j : B →ₐ[R] E) (h : E →ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal R) R),
      h.comp j = g := by sorry
