-- Prove2me | Theorems.Thm_MasulloRH_rational_adele_theta_image
-- name    : MasulloRH.rational_adele_theta_image
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:11:38.296183+00:00
-- url     : https://prove2.me/theorems/60bad344-cc9f-4a1c-886c-d8f8d5641506
-- title:
--   Exact spherical theta image of the full rational adelic Schwartz–Bruhat space
-- statement:
--   Average the rational-diagonal theta sum of a Schwartz–Bruhat test $F$ on the full rational adèle ring over integral idèle units. For every $t>0$ the sums converge absolutely, the unit orbit sum is integrable, and its average equals $\sum_{n\in\mathbb Z}g(nt)$ for one real-place Schwartz test $g$. The value at zero is $g(0)=F(0)$, and the integral of $F$ is the additive Haar mass of the standard rational adelic box times $\int g$. Conversely, every $g$ occurs through the explicit lift $g\otimes 1_{\widehat{\mathbb Z}}$. Thus the images agree exactly for tests satisfying the two vanishing moment conditions.
-- source:
--   A. M. Masullo, The Music of the Primes, rational trivial-character norm component of §§10.1–10.2, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Appendix I, https://arxiv.org/abs/math/9811068. The identification of the adelic image was raised explicitly in https://github.com/mccorvie/riemann-masullo/issues/1169#issuecomment-7053478224. Uses rational spherical finite-adèle synthesis 6abb1b0f and the proved number-field adelic box measure and diagonal theorems.

import Definitions.Def_MasulloRH_RationalFiniteRadial
import Definitions.Def_NumberField_AdelicFourier
open NumberField IsDedekindDomain MeasureTheory MasulloRH.RationalFinite
open scoped Classical SchwartzMap

theorem MasulloRH.rational_adele_theta_image [MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)] [BorelSpace (AdeleRing (𝓞 ℚ) ℚ)]
    (μ : Measure (AdeleRing (𝓞 ℚ) ℚ)) [μ.IsAddHaarMeasure]
    [MeasurableSpace K] [BorelSpace K] (κ : Measure K) [κ.IsMulLeftInvariant] [IsProbabilityMeasure κ] :
    let orbit (t : ℝ) (u : K) (q : ℚ) : AdeleRing (𝓞 ℚ) ℚ :=
      let dilation : AdeleRing (𝓞 ℚ) ℚ := ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm
        (algebraMap ℝ (mixedEmbedding.mixedSpace ℚ) t), (u.val : A))
      dilation * algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q
    let adelicTheta (F : AdeleRing (𝓞 ℚ) ℚ → ℂ) (t : ℝ) := ∫ u : K, ∑' q : ℚ, F (orbit t u q) ∂κ
    let realTheta (g : 𝓢(ℝ,ℂ)) (t : ℝ) := ∑' n : ℤ, g ((n:ℝ)*t)
    (∀ F ∈ AdelicFourier.schwartzBruhat ℚ,
      (∀ t : ℝ, 0<t → (∀ u : K, Summable (fun q : ℚ => ‖F (orbit t u q)‖)) ∧
        Integrable (fun u : K => ∑' q : ℚ, F (orbit t u q)) κ) ∧
      ∃ g : 𝓢(ℝ,ℂ), g 0 = F 0 ∧
        (∫ x, F x ∂μ) = (μ.real (AdelicBox.adelicBox ℚ) : ℂ) * (∫ x : ℝ, g x) ∧
        ∀ t : ℝ, 0<t → adelicTheta F t = realTheta g t) ∧
    (∀ g : 𝓢(ℝ,ℂ),
      let F (x : AdeleRing (𝓞 ℚ) ℚ) :=
        g ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1).1
          ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩) * O.indicator (1 : A → ℂ) x.2
      F ∈ AdelicFourier.schwartzBruhat ℚ ∧ g 0 = F 0 ∧
        (∫ x, F x ∂μ) = (μ.real (AdelicBox.adelicBox ℚ) : ℂ) * (∫ x : ℝ, g x) ∧
        ∀ t : ℝ, 0<t → adelicTheta F t = realTheta g t) ∧
    {Φ : {t : ℝ // 0<t} → ℂ | ∃ F ∈ AdelicFourier.schwartzBruhat ℚ,
      F 0 = 0 ∧ (∫ x, F x ∂μ) = 0 ∧ ∀ t, Φ t = adelicTheta F t.1} =
    {Φ : {t : ℝ // 0<t} → ℂ | ∃ g : 𝓢(ℝ,ℂ),
      g 0 = 0 ∧ (∫ x : ℝ, g x) = 0 ∧ ∀ t, Φ t = realTheta g t.1} := by sorry
