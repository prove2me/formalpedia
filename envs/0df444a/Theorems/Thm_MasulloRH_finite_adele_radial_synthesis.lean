-- Prove2me | Theorems.Thm_MasulloRH_finite_adele_radial_synthesis
-- name    : MasulloRH.finite_adele_radial_synthesis
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:40:38.211006+00:00
-- url     : https://prove2.me/theorems/6abb1b0f-13ee-4a39-af8b-52f920a0efa0
-- title:
--   The spherical finite-adèle Bruhat tests over the rationals are spanned by dilated integral lattices
-- statement:
--   Let $O=\widehat{\mathbb Z}$ inside the rational finite adèles $A$, and give $K=O^\times$ its Haar probability measure. The image of compactly supported locally constant complex functions on $A$ under $h\mapsto[x\mapsto\int_Kh(ux)\,du]$ is exactly the complex span of the indicators $\mathbf1_{dO}$ for $d\in\mathbb Q_{>0}$. This span also consists exactly of the $K$-invariant compactly supported locally constant functions.
--
--   More explicitly, if $N\ge1$, $a\in\mathbb Z$ is a unit modulo $N$, and $b\in\mathbb Q^\times$, then every $x\in A$ satisfies
--   $$
--   \int_K \mathbf1_{ba+bNO}(ux)\,du =
--   \frac{1}{\varphi(N)}\sum_{e\mid N}\mu(e)\,\mathbf1_{|be|O}(x).
--   $$
--   The formula holds throughout the finite adèle ring. It gives the finite-place averaging step for the trivial norm-character part of the rational theta construction.
-- source:
--   A. M. Masullo, The Music of the Primes, Example 2.1.3.1, pp. 67–68, Definition 2.2.3.1 and (A.2.2.1)–(A.2.2.3). A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, §III and Appendix I, https://arxiv.org/abs/math/9811068. The explicit Möbius formula is a derivation for the rational finite-unit projection. Reuses the proved common-level adèle coset decomposition of NumberField.AdelicBox and the rational unit-residue congruence of RatIdele.

import Mathlib
import Definitions.Def_MasulloRH_RationalFiniteRadial
open NumberField IsDedekindDomain MeasureTheory MasulloRH.RationalFinite
open scoped BigOperators

theorem MasulloRH.finite_adele_radial_synthesis [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [μ.IsMulLeftInvariant] [IsProbabilityMeasure μ] :
    (∀ f : A→ℂ, (f ∈ radialSpan ↔ ∃ h : A→ℂ, IsLocallyConstant h ∧ HasCompactSupport h ∧
      ∀ x : A, f x = ∫ u : K, h ((u.val:A)*x) ∂μ) ∧
      (f ∈ radialSpan ↔ IsLocallyConstant f ∧ HasCompactSupport f ∧
        ∀ u : K, ∀ x : A, f ((u.val:A)*x) = f x)) ∧
    (∀ (N : ℕ) [NeZero N] (a : ℤ), IsUnit (a:ZMod N) → ∀ (b : ℚ), b ≠ 0 →
      ∀ x : A, (∫ u : K, (translatedBall (b*(a:ℚ)) (b*(N:ℚ))).indicator (1:A→ℂ)
        ((u.val:A)*x) ∂μ) = ((N.totient:ℂ)⁻¹ • ∑ e ∈ N.divisors, (ArithmeticFunction.moebius e:ℂ) •
          (centeredBall |b*(e:ℚ)|).indicator (1:A→ℂ)) x) := by sorry
