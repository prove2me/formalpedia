-- Prove2me | Theorems.Thm_MasulloAudit_prime_shell_quotient_closed_spaces_coincide
-- name    : MasulloAudit.prime_shell_quotient_closed_spaces_coincide
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:19:44.952435+00:00
-- url     : https://prove2.me/theorems/f6381af1-bfc0-45e8-bc5e-ecd2882611a3
-- title:
--   On the rational idèle class group the empty and one-prime truncated spherical spaces coincide at every width
-- statement:
--   Let $C=\mathbb A_{\mathbb Q}^{\times}/\mathbb Q^\times$, $t=\log |z|$, and $K=\widehat{\mathbb Z}^{\times}$. Use probability Haar on $K$ and normalize Haar on $C$ to give Lebesgue measure under $t$. Work in the full class-group Hilbert space with weight $1+t^2$ (Masullo's $s=2$). For every admissible Schwartz–Bruhat test, its ordinary rational orbital sum averaged over $K$ lies in this weighted space even before truncation. For any measurable $S\subseteq[a,\infty)$ and any rational prime $p$, the closed masked image of all admissible tests coincides with the closed masked image of actual one-place principal values of spherical pure tensors. Both equal the isometric pullback of the entire real weighted $L^2$ subspace supported on $S$. This holds for every intermediate admissible test family containing those prime differences. The orthogonal difference is zero. In particular it covers each positive cutoff and each two-sided cutoff, at every width, in the rational trivial-character case of (11.1.2.6).
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Theorem 11.1.2.1(2), pp. 480–482, especially (11.1.2.3), (11.1.2.6), (11.1.2.9) and the inference after (11.1.2.16). Rational field, trivial character, empty versus singleton set of additional finite places, Sobolev exponent two.

import Definitions.Def_Masullo_RationalQuotientShell
open MeasureTheory Set NumberField IsDedekindDomain
open MasulloRH.RationalFinite MasulloRH.RationalClass
open MasulloAudit.RationalQuotientShell MasulloAudit.RationalSphericalCutoff
open scoped ENNReal InnerProductSpace

theorem MasulloAudit.prime_shell_quotient_closed_spaces_coincide [MeasurableSpace K] [BorelSpace K] [MeasurableSpace C] [BorelSpace C] :
    ∃ κ : Measure K, κ.IsHaarMeasure ∧ IsProbabilityMeasure κ ∧
    ∃ ν : Measure C, ν.IsHaarMeasure ∧ MeasurePreserving logNorm ν volume ∧
    ∃ J : Lp ℂ 2 realMeasure →ₗᵢ[ℂ] Lp ℂ 2 (classMeasure ν),
      (∀ w, (J w : C → ℂ) =ᵐ[classMeasure ν] fun z => w (logNorm z)) ∧
      (∀ F, Admissible F → MemLp (sphericalTheta κ F) 2 (classMeasure ν)) ∧
      ∀ (p : Nat.Primes) (a : ℝ) (s : Set ℝ), MeasurableSet s → s ⊆ Ici a →
        (∀ B : Set (Ad → ℂ), primeSources p ⊆ B → B ⊆ {F | Admissible F} →
          closure (testImage κ ν s B) = J '' supported realMeasure s) ∧
        closure (testImage κ ν s (primeSources p)) = closure (testImage κ ν s {F | Admissible F}) ∧
        ∀ v ∈ closure (testImage κ ν s {F | Admissible F}),
          (∀ u ∈ closure (testImage κ ν s (primeSources p)), inner ℂ u v=0) → v=0 := by sorry
