-- Prove2me | Theorems.Thm_MasulloRH_rational_idele_class_spherical_coordinates
-- name    : MasulloRH.rational_idele_class_spherical_coordinates
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:41:13.66317+00:00
-- url     : https://prove2.me/theorems/ee89b802-6f0b-405f-83dd-d190b4bff612
-- title:
--   Rational idèle-class disintegration, spherical theta image and orthogonal projection
-- statement:
--   The actual group of rational idèle classes is multiplicatively homeomorphic to the product of the logarithmic real coordinate and the finite integral idèle units. Its norm agrees with the canonical Tate norm and its norm-one subgroup is compact. Under the Haar normalization giving the finite units mass one, the quotient Haar measure is Lebesgue measure in the log coordinate times Haar probability, and any logarithmic slab of width L has mass L. On the quotient itself, unit-averaged orbital theta images of admissible global Schwartz–Bruhat tests are exactly the bilateral theta profiles of admissible real Schwartz functions. Pullback by the log norm is an isometry onto the closed finite-unit invariant sector in quotient L². The orthogonal projection onto this sector is averaging over the finite-unit orbit, with almost-everywhere absolute integrability for every L² vector.
-- source:
--   A. M. Masullo, The Music of the Primes, rational trivial-character specialization of Chapters 9–10, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Appendix I, https://arxiv.org/abs/math/9811068. The adelic image comparison is discussed in https://github.com/mccorvie/riemann-masullo/issues/1169#issuecomment-7053478224. Uses the established spherical image 60bad344, the rational idèle normalizer, and the certified Tate Haar-character identities. A positive real representative factorization also appears inside the proof of RatIdele.exists_norm_apply_eq_ideleNorm_rpow (64e236c7).

import Definitions.Def_MasulloRH_RationalIdeleClass
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
open NumberField IsDedekindDomain MeasureTheory Set
open MasulloRH.RationalFinite MasulloRH.RationalClass
open scoped Topology ENNReal SchwartzMap InnerProductSpace

theorem MasulloRH.rational_idele_class_spherical_coordinates [MeasurableSpace Ad] [BorelSpace Ad] (μ : Measure Ad) [μ.IsAddHaarMeasure]
    [MeasurableSpace K] [BorelSpace K] [mC : MeasurableSpace C] [bC : BorelSpace C] :
    (∀ x : I, normHom (classOf x) = TateGlobal.ideleNorm ℚ x) ∧ CompactSpace normHom.ker ∧
    (∃ κ : Measure K, κ.IsHaarMeasure ∧ IsProbabilityMeasure κ) ∧
    ∃ e : Multiplicative ℝ × K ≃ₜ* C,
      (∀ s : Multiplicative ℝ, ∀ u : K, ∃ x : I,
        (x:Ad) = ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm
          (algebraMap ℝ (mixedEmbedding.mixedSpace ℚ) (Real.exp s.toAdd)), (u.val:A)) ∧
        classOf x = e (s,u) ∧ logNorm (classOf x) = s.toAdd) ∧
      (∀ u : K, finiteUnit u = e (1,u)) ∧
      ∀ (κ : Measure K) [κ.IsMulLeftInvariant] [IsProbabilityMeasure κ],
        let h := fun v : ℝ × K => e (Multiplicative.ofAdd v.1,v.2)
        ∃ ν : Measure C, ν.IsHaarMeasure ∧
          MeasurePreserving h ((volume : Measure ℝ).prod κ) ν ∧
          MeasurePreserving logNorm ν (volume : Measure ℝ) ∧
          (∀ a b : ℝ, ν (h '' (Icc a b ×ˢ univ)) = ENNReal.ofReal (b-a)) ∧
          (∀ F : C → ℂ, Integrable F ν → (∫ z, F z ∂ν) =
            ∫ x : ℝ, ∫ u : K, F (e (Multiplicative.ofAdd x,u)) ∂κ) ∧
          {Φ : C → ℂ | ∃ F ∈ AdelicFourier.schwartzBruhat ℚ, F 0=0 ∧ (∫ a, F a ∂μ)=0 ∧
              Φ = sphericalTheta κ F} =
            {Φ : C → ℂ | ∃ g : 𝓢(ℝ,ℂ), g 0=0 ∧ (∫ x : ℝ, g x)=0 ∧
              ∀ z, Φ z = ∑' n : ℤ, g ((n:ℝ)*Real.exp (logNorm z))} ∧
          ∃ J : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 ν,
            (∀ g, (J g : C → ℂ) =ᵐ[ν] fun z => g (logNorm z)) ∧
            IsClosed (J.toLinearMap.range : Set (Lp ℂ 2 ν)) ∧
            (∀ F : Lp ℂ 2 ν, F ∈ J.toLinearMap.range ↔
               ∀ᵐ z ∂ν, ∀ᵐ u ∂κ, F (z*finiteUnit u) = F z) ∧
            ∃ P : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν, ∀ F : Lp ℂ 2 ν,
              P F ∈ J.toLinearMap.range ∧ F-P F ∈ J.toLinearMap.rangeᗮ ∧
              (∀ᵐ z ∂ν, Integrable (fun u : K => F (z*finiteUnit u)) κ) ∧
              (P F : C → ℂ) =ᵐ[ν] fun z => ∫ u : K, F (z*finiteUnit u) ∂κ := by sorry
