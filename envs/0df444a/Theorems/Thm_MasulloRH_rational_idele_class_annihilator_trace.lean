-- Prove2me | Theorems.Thm_MasulloRH_rational_idele_class_annihilator_trace
-- name    : MasulloRH.rational_idele_class_annihilator_trace
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:52:47.136908+00:00
-- url     : https://prove2.me/theorems/5cf19dfc-f6e2-4d5a-8ee9-48c7d5af0b56
-- title:
--   The spherical theta-annihilator on actual rational idèle classes and its nuclear zero-jet trace
-- statement:
--   Equip rational idèle classes with the normalized Haar product of Lebesgue log coordinate and compact finite-unit Haar probability. For p>1/2, the intrinsic annihilator of all admissible global Schwartz–Bruhat spherical theta tests in the finite-unit invariant sector is unitarily equivalent to the real theta annihilator by pullback along the actual log norm. It equals the closed span of critical-line zeta jets of order r below the zero multiplicity and satisfying r+1/2<p. For every admissible convolution test there is exactly one nuclear operator with the stated physical matrix coefficients on actual idèle classes, and its trace is the weighted sum of the Mellin test over critical-line zeros with multiplicity capped by ceil(p−1/2).
-- source:
--   A. M. Masullo, The Music of the Primes, rational trivial-character specialization of Chapters 9 and 10, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. The actual global theta-space identification was raised in https://github.com/mccorvie/riemann-masullo/issues/1169#issuecomment-7053478224. Uses the verified actual quotient chart, image and Haar projection ee89b802, real theta-annihilator trace 5f60b4c6, and basis-independent nuclear trace edf55f93. The width here is zero; the parameter p counts polynomial logarithmic weight and controls jet order.

import Definitions.Def_MasulloRH_RationalClassThetaSpace
import Definitions.Def_MasulloRH_RationalThetaSpace
import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_MasulloGRH_HilbertNuclear
open NumberField IsDedekindDomain MeasureTheory Set
open MasulloGRH MasulloRH MasulloRH.RationalFinite MasulloRH.RationalClass
open scoped Topology InnerProductSpace SchwartzMap ENNReal

theorem MasulloRH.rational_idele_class_annihilator_trace [MeasurableSpace Ad] [BorelSpace Ad] (μ : Measure Ad) [μ.IsAddHaarMeasure]
    [MeasurableSpace K] [BorelSpace K] (κ : Measure K) [κ.IsMulLeftInvariant] [IsProbabilityMeasure κ]
    [MeasurableSpace C] [BorelSpace C] :
    ∃ (e : Multiplicative ℝ × K ≃ₜ* C) (ν : Measure C), ν.IsHaarMeasure ∧
      MeasurePreserving (fun v : ℝ × K => e (Multiplicative.ofAdd v.1,v.2)) ((volume : Measure ℝ).prod κ) ν ∧
      (∀ x u, logNorm (e (Multiplicative.ofAdd x,u))=x) ∧ (∀ u : K, finiteUnit u=e (1,u)) ∧
      ∀ p : ℝ, 1/2<p →
        let Z := {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}
        let V := rationalClassThetaAnnihilator μ κ ν p
        (∃ E : rationalThetaAnnihilator p ≃ₗᵢ[ℂ] V, ∀ f,
          ((E f : Lp ℂ 2 ν) : C→ℂ) =ᵐ[ν] fun z => (f : Lp ℂ 2 (volume : Measure ℝ)) (logNorm z)) ∧
        V = (Submodule.span ℂ {v : Lp ℂ 2 ν | ∃ (z : Z) (r : ℕ),
          r<analyticOrderNatAt riemannZeta z.val ∧ (r:ℝ)+1/2<p ∧
          (v:C→ℂ) =ᵐ[ν] fun q =>
            ((1+(logNorm q)^2)^(-p/2):ℝ) * (((logNorm q:ℝ):ℂ)^r *
              Complex.exp (↑(z.val.im*logNorm q)*Complex.I))}).topologicalClosure ∧
        ∀ (φ : ℝ→ℂ), IsRationalTraceTest φ →
          ∃! T : V →L[ℂ] V,
            IsRationalClassThetaConvolution μ κ ν p (fun y => e (Multiplicative.ofAdd y,1)) φ T ∧
            IsNuclearOperator T ∧
            HasSum (fun z : Z => ((min (analyticOrderNatAt riemannZeta z.val) ⌈p-1/2⌉₊:ℕ):ℂ) *
              mellin φ (z.val-1/2)) (operatorTrace T) := by sorry
