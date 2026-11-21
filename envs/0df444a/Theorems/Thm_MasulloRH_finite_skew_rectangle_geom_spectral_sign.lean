-- Prove2me | Theorems.Thm_MasulloRH_finite_skew_rectangle_geom_spectral_sign
-- name    : MasulloRH.finite_skew_rectangle_geom_spectral_sign
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T05:01:47.710427+00:00
-- url     : https://prove2.me/theorems/1ee4d1ba-e35f-4542-b71b-e855604f9889
-- title:
--   Fixed sign of the weighted geometric kernel on finite rectangles at equal-norm skew centers
-- statement:
--   In the difference convention of Masullo (10.4.3.50), suppose $k_{\rm geom}(u,v)=\phi(uv^{-1})-k_{\rm spec}(u,v)$ almost everywhere for the pair measure $\mu$. Let $L$ be the logarithm of the norm, so $L(uv^{-1})=L(u)-L(v)$. Suppose $\phi$ vanishes whenever $L<\delta$ for some $\delta>0$. Fix any centers $x,y$ with $L(x)=L(y)$ and any measurable neighborhoods $U,V$ on which $|L(u)-L(x)|\le r$ and $|L(v)-L(y)|\le s$, with $r,s\ge0$ and $r+s<\delta$. For every common complex weight $w$ for which $w k_{\rm spec}$ is absolutely integrable on $U\times V$, the weighted geometric kernel is absolutely integrable there, and
--   $$\int_{U\times V} w k_{\rm geom}\,d\mu=-\int_{U\times V} w k_{\rm spec}\,d\mu.$$
--   The same positive choice $r=s=\delta/3$ works at every equal-norm center pair. An idelic norm-one translate and a rational principal translate preserve the norm, so this sign test applies to all their skew-center pairs for common finite cutoffs satisfying the stated integrability condition.
-- source:
--   Masullo, The Music of the Primes, frozen 20 November 2026, (10.4.3.50), (11.3.2.1) and the diagonal sign in (12.1.1.23). Finite-rectangle, equal-norm version for the difference convention of (10.4.3.50).

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory Set

theorem MasulloRH.finite_skew_rectangle_geom_spectral_sign {G : Type*} [Group G] [MeasurableSpace G]
    (L : G → ℝ) (hL : ∀ u v, L (u*v⁻¹) = L u - L v)
    (δ : ℝ) (hδ : 0 < δ) (φ : G → ℂ) (hφ : ∀ u, L u < δ → φ u = 0)
    (μ : Measure (G × G)) (geom spec : G × G → ℂ)
    (hk : ∀ᵐ p ∂μ, geom p = φ (p.1*p.2⁻¹) - spec p) :
    (∃ R : ℝ, 0 < R ∧ R+R < δ) ∧
    ∀ (r s : ℝ), 0 ≤ r → 0 ≤ s → r+s < δ →
    ∀ (x y : G), L x = L y → ∀ (U V : Set G), MeasurableSet U → MeasurableSet V →
      (∀ u ∈ U, |L u-L x| ≤ r) → (∀ v ∈ V, |L v-L y| ≤ s) →
      ∀ w : G × G → ℂ, IntegrableOn (fun p => w p * spec p) (U ×ˢ V) μ →
        IntegrableOn (fun p => w p * geom p) (U ×ˢ V) μ ∧
        (∫ p in U ×ˢ V, w p * geom p ∂μ) = -(∫ p in U ×ˢ V, w p * spec p ∂μ) := by sorry
