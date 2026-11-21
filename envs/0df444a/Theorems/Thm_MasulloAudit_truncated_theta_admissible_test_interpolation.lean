-- Prove2me | Theorems.Thm_MasulloAudit_truncated_theta_admissible_test_interpolation
-- name    : MasulloAudit.truncated_theta_admissible_test_interpolation
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:31:56.958199+00:00
-- url     : https://prove2.me/theorems/82df3338-f7db-4d32-9904-b17761ddf654
-- title:
--   Exact interpolation above a cutoff by rational adelic theta series with any finite set of unit conditions
-- statement:
--   Fix $a>0$, a finite set $T$ of rational primes and a smooth compactly supported $g:\mathbb R\to\mathbb C$ vanishing on $(-\infty,0]$. There is a smooth compactly supported $f$ vanishing there with $\int f=0$. Put $U=\widehat{\mathbb Z}$ and take the adelic test
--   $$\Phi(y)=f(y_\infty)\,1_U(y_f)\prod_{p\in T}(1-1_U(y_f/p)).$$
--   Then $\Phi$ is Schwartz–Bruhat on $\mathbb A_{\mathbb Q}$, $\Phi(0)=0$ and its integral against every additive Haar measure is zero. On every idele $z$ with $z_f,z_f^{-1}\in U$ and $z_\infty\ge a$, its unconditionally summable rational orbital series has the exact value $\sum_{q\in\mathbb Q^\times}\Phi(qz)=g(z_\infty)$. This gives a common space of smooth truncated targets with and without any prescribed finite set of prime-unit conditions at the original adelic test-function level.
-- source:
--   A. M. Masullo, The Music of the Primes, 20 November 2026 draft, Chapter 11, Theorem 11.1.2.1(2)–(3), especially equations (11.1.2.6)–(11.1.2.9), pp. 480–481. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicLevel

open NumberField IsDedekindDomain MeasureTheory Set
open scoped ContDiff Classical

noncomputable local instance : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) :=
  (borel (InfiniteAdeleRing ℚ)).prod (borel (FiniteAdeleRing (𝓞 ℚ) ℚ))

theorem MasulloAudit.truncated_theta_admissible_test_interpolation (T : Finset Nat.Primes) (a : ℝ) (ha : 0<a) (g : ℝ→ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hg₀ : ∀ x,x≤0 → g x=0) :
    let r := fun y : AdeleRing (𝓞 ℚ) ℚ => (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ y.1).1 ⟨Rat.infinitePlace,Rat.isReal_infinitePlace⟩
    let U := AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ
    ∃ (f : ℝ→ℂ) (Φ : AdeleRing (𝓞 ℚ) ℚ→ℂ),
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ x,x≤0 → f x=0) ∧ (∫ x,f x)=0 ∧
      (∀ y,Φ y=if y.2∈U ∧ ∀ p∈T,(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (p:ℚ)⁻¹).2*y.2∉U then f (r y) else 0) ∧
      Φ∈AdelicFourier.schwartzBruhat ℚ ∧ Φ 0=0 ∧
      (∀ (ν : Measure (AdeleRing (𝓞 ℚ) ℚ)) [ν.IsAddHaarMeasure], (∫ x,Φ x ∂ν)=0) ∧
      ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (z:AdeleRing (𝓞 ℚ) ℚ).2∈U → (↑z⁻¹:AdeleRing (𝓞 ℚ) ℚ).2∈U → a≤r z →
        HasSum (fun q : ℚˣ => Φ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (q:ℚ)*z)) (g (r z)) := by sorry
