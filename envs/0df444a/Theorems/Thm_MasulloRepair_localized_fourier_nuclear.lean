-- Prove2me | Theorems.Thm_MasulloRepair_localized_fourier_nuclear
-- name    : MasulloRepair.localized_fourier_nuclear
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T20:06:01.529338+00:00
-- url     : https://prove2.me/theorems/e4f314db-7458-4e45-a40e-404807300b2c
-- title:
--   Localized Fourier smoothing is nuclear for every integrable symbol and L2 masks
-- statement:
--   Let $a,b\in L^2(\mathbb R)$ and $m\in L^1(\mathbb R)$ be complex-valued functions. Use the Fourier character
--   $$\chi(x,\xi)=e^{2\pi i x\xi}.$$
--   There exists a bounded nuclear operator $T$ on $L^2(\mathbb R)$ such that, for every $u\in L^2(\mathbb R)$, almost everywhere in $x$,
--   $$Tu(x)=a(x)\int_{\mathbb R}m(\xi)\chi(x,\xi)
--   \left(\int_{\mathbb R}\overline{\chi(y,\xi)}b(y)u(y)\,dy\right)d\xi,$$
--   and also
--   $$Tu(x)=a(x)\int_{\mathbb R}\kappa_m(x-y)b(y)u(y)\,dy,
--   \qquad \kappa_m(t)=\int_{\mathbb R}m(\xi)e^{2\pi i t\xi}\,d\xi.$$
--   The trace norm satisfies
--   $$\|T\|_{\mathrm{Tr}}\le\|a\|_2\,\|b\|_2\,\|m\|_1.$$
--
--   The masks need only be square-integrable; no smoothness, compact support, or boundedness is required. The Fourier symbol can be complex and can vanish. This supplies a quantitative trace-class construction for localized Fourier smoothing. For spatial interval indicators, the bound specializes to the square root of the product of their lengths times the $L^1$ norm of the symbol.
--
--   Both the frequency expression and its spatial convolution representation are included in the formal theorem. Identifying a particular physical theta operator or proving convergence of its range projections remains an application-specific step.
-- source:
--   Auxiliary smoothing theorem for Yi's 'Exact spatial distribution of the prime atom, and a test of reciprocal inversion as a repair of (11.3.2.4)', https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-26b2fce9-9b7f-4e53-be0e-981993a5ae05, paragraph 'Why the actual compact-window limit has an explicit kernel here': the nuclearity of compactly restricted convolution by Fourier factorization. Also supports step 4 of the fixed-prime calculation, https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-a91427c0-0f6d-4e33-aa30-fe6dd8cddd02. This is an unconditional analytic ingredient of the proposed repair; none of the source's arithmetic range or zero-free assertions is an assumption or conclusion here. The general L2-mask/L1-symbol statement and its square-root factorization are supplied here as the precise analytic lemma behind the source's compact Fourier smoothing claim. Fourier convention: exp(2*pi*i*x*xi).

import Definitions.Def_MasulloGRH_HilbertNuclear
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Complex.Log
set_option autoImplicit false
open MasulloGRH MeasureTheory

theorem MasulloRepair.localized_fourier_nuclear (a b m : ℝ → ℂ) (ha : MemLp a 2 volume)
    (hb : MemLp b 2 volume) (hm : Integrable m volume) :
    let χ : ℝ → ℝ → ℂ := fun x ξ =>
      Complex.exp (((2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)
    ∃ T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      (∀ u : Lp ℂ 2 (volume : Measure ℝ), ∀ᵐ x ∂volume,
        T u x = a x * ∫ ξ, m ξ * χ x ξ * (∫ y, star (χ y ξ) * b y * u y) ∧
        T u x = a x * ∫ y, (∫ ξ, m ξ * χ (x - y) ξ) * b y * u y) ∧
      IsNuclearOperator T ∧
      traceNorm T ≤ (eLpNorm a 2 volume).toReal * (eLpNorm b 2 volume).toReal *
        ∫ ξ, ‖m ξ‖ := by sorry
