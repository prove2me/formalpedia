-- Prove2me | Theorems.Thm_MasulloRH_rational_two_place_lower_log_window
-- name    : MasulloRH.rational_two_place_lower_log_window
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T03:04:12.237184+00:00
-- url     : https://prove2.me/theorems/8c87cfbe-147f-409b-9599-30431972b7ce
-- title:
--   Bilateral prime-power lower-window estimate on the real and p-adic places of the rationals
-- statement:
--   Take the two places ℝ and ℚₚ of the rationals. For every k∈ℤ, modulate f(x) by exp(2πiηpᵏx) and g(y) by the additive character ψ(ηₚpᵏy), with |η|=‖ηₚ‖ₚ=1. Let u=log|x|+log‖y‖ₚ, and integrate the product against the difference of the one-sided and two-sided window lengths, (U+V−u)₊−(U−max(−W,u−V))₊, using Lebesgue measure and the specified additive measure on ℚₚ. If −W≤U, this lower-window defect Dₖ is absolutely summable in k. For every 0<δ<1 its total absolute mass is at most (A∞Hₚ+AₚH∞) exp(δ(V−W))/(δ(1−p^(−(1−δ)))). The amplitude constants and negative local moments H appear explicitly in the formal statement. Hypotheses are bounded integrable C¹ real data with integrable derivative, and bounded supported p-adic data invariant under a ball of translations. The additive p-adic measure is σ-finite and translation invariant, with μ(B(0,r))≤Vₚr; ψ is measurable, bounded in modulus by one, and nontrivial at p⁻¹. The choices of local units include both signs of every rational S-unit ±pᵏ.
-- source:
--   Two-place lower-cutoff estimate for the rational relative trace comparison in the Masullo mission. The local real primitive is proved by integration by parts; the p-adic ball primitive uses translation cancellation. The full weighted product-measure estimate, Fourier phases, frequency rays, local integrability and normalization bookkeeping are included in the submitted proof. Related source context: Masullo, The Music of the Primes, chapter 12, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf .

import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.RealDeriv

open MeasureTheory Set Filter
open scoped Padic ENNReal

theorem MasulloRH.rational_two_place_lower_log_window (p : ℕ) [Fact p.Prime]
    [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] (μ : Measure ℚ_[p]) [SigmaFinite μ] [μ.IsAddLeftInvariant]
    (ψ : AddChar ℚ_[p] ℂ) (hψm : Measurable ψ) (hψ : ψ ((p:ℚ_[p])⁻¹) ≠ 1)
    (hunit : ∀ z, ‖ψ z‖ ≤ 1)
    (f : ℝ → ℂ) (g : ℚ_[p] → ℂ) (hf : ContDiff ℝ 1 f)
    (hi : Integrable f) (hdif : Integrable (deriv f)) (hgm : Measurable g)
    (Mr Vp Mp Rp Lp : ℝ) (hMr : 0≤Mr) (hV : 0≤Vp) (hM : 0≤Mp) (hR : 0<Rp) (hL : 0<Lp)
    (hμ : ∀ r : ℝ, 0<r → μ (Metric.ball 0 r) ≤ ENNReal.ofReal (Vp*r))
    (hfB : ∀ x, ‖f x‖≤Mr) (hgB : ∀ y, ‖g y‖≤Mp) (hgS : ∀ y, Rp≤‖y‖ → g y=0)
    (hgP : ∀ y d : ℚ_[p], ‖d‖≤Lp → g (d+y)=g y)
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (η : ℝ) (ηp : ℚ_[p]) (hη : |η|=1) (hηp : ‖ηp‖=1)
    (U V W : ℝ) (hUV : -W≤U) :
    let v (x : ℝ × ℚ_[p]) := Real.log ‖x.1‖ + Real.log ‖x.2‖
    let F (k : ℤ) (x : ℝ) := f x * Complex.exp
      (((2*Real.pi*(η*(p:ℝ)^k):ℝ):ℂ)*Complex.I*(x:ℂ))
    let G (k : ℤ) (y : ℚ_[p]) := g y * ψ ((ηp*(p:ℚ_[p])^k)*y)
    let D (k : ℤ) := ∫ x : ℝ × ℚ_[p],
      (max (U+V-v x) 0 - max (U-max (-W) (v x-V)) 0) • (F k x.1 * G k x.2)
      ∂(volume.prod μ)
    let Ar := max (2*Mr) ((2*Mr+∫ x, ‖deriv f x‖)/(2*Real.pi))
    let Ap := Mp*Vp*max 1 (max (p:ℝ) (Rp*max 1 ((p:ℝ)/Lp)))
    let Hr := ∫ x : ℝ, Real.exp (-δ*Real.log ‖x‖)*‖f x‖
    let Hp := ∫ y : ℚ_[p], Real.exp (-δ*Real.log ‖y‖)*‖g y‖ ∂μ
    Summable (fun k : ℤ => ‖D k‖) ∧
    (∑' k : ℤ, ‖D k‖) ≤ (Ar*Hp+Ap*Hr)/(1-Real.exp (-(1-δ)*Real.log (p:ℝ))) *
       (Real.exp (δ*(V-W))/δ) := by sorry
