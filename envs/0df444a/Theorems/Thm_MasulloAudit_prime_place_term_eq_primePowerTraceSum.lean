-- Prove2me | Theorems.Thm_MasulloAudit_prime_place_term_eq_primePowerTraceSum
-- name    : MasulloAudit.prime_place_term_eq_primePowerTraceSum
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:35:13.983636+00:00
-- url     : https://prove2.me/theorems/14e52cb1-68be-4692-8e9d-f2d461a61d79
-- title:
--   Prime-place term of Masullo's Theorem 12.5.1.1 for $\mathbf Q$ equals the formal prime-power sum
-- statement:
--   Let $p$ be a prime and $\mu$ any additive Haar measure on $\mathbf Q_p$, giving the multiplicative Haar measure $d\mu^\times(g)=d\mu(g)/|g|_p$ on $\mathbf Q_p^\times$. Let $\varphi$ be an admissible test (`MasulloRH.IsRationalTraceTest`: smooth, compactly supported in $(0,\infty)$, $\varphi(1)=0$), regarded as the norm-invariant function $g\mapsto\varphi(|g|_p)$. Then the prime-place term of Masullo's Theorem 12.5.1.1 converges absolutely and
--
--   $$
--   \frac{\log p}{\mu(\mathbf Z_p^\times)}\int_{\mathbf Q_p^\times}\varphi(|g|_p)\,\frac{|g|_p^{1/2}}{|1-g|_p}\,\frac{d\mu(g)}{|g|_p}=\sum_{k\ge1}\frac{\log p}{p^{k/2}}\bigl(\varphi(p^k)+\varphi(p^{-k})\bigr).
--   $$
--
--   The right side is the prime-$p$ part of `MasulloRH.primePowerTraceTerm`, used in the formalization `MasulloRH.trace_formula_rational`. This shows that the formalization evaluates the source's finite-place terms ((12.5.1.2), p. 519, with weight $\log q_v/\mu_v(\mathcal O_{F_v}^\times)$) correctly, independently of the normalization of Haar measure. The companion result `MasulloAudit.real_place_term_eq_realTraceIntegral` does the same for the real place.
--
--   **Formalization Note.** Mathlib at this revision provides no measurable structure or Haar measure on $\mathbf Q_p$, so the statement takes `[MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]` and an arbitrary `μ` with `IsAddHaarMeasure`. $\mu(\mathbf Z_p^\times)$ is `μ.real {g | ‖g‖ = 1}`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 12.5.1.1, eq. (12.5.1.2), p. 519.

import Definitions.Def_MasulloRH_RationalTrace
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace MasulloAudit

open MasulloRH

/-- Prime-place term of Masullo, Theorem 12.5.1.1 (ζ case), at a prime `p`, for
norm-invariant tests. For `φ(g) = ϕ(|g|_p)` with `ϕ` an admissible rational trace test
(smooth, compact support in `(0,∞)`, `ϕ 1 = 0`), and the Haar measure
`dμ_p = dx/|x|_p` on `ℚ_p^×` built from an arbitrary additive Haar measure `μ` on `ℚ_[p]`
(so `μ_p(ℤ_p^×) = μ {‖g‖ = 1}`), the term
`(log p / μ_p(ℤ_p^×)) ∫_{ℚ_p^×} φ(g) |g|_p^{1/2} / |1 - g|_p dμ_p(g)` is an absolutely
convergent integral and equals `Σ_{k ≥ 0} primePowerTraceTerm ϕ (p, k)`, i.e.
`Σ_{k ≥ 1} (log p) p^{-k/2} (ϕ(p^k) + ϕ(p^{-k}))`. -/
theorem prime_place_term_eq_primePowerTraceSum (p : ℕ) [hp : Fact p.Prime]
    [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (fun g : ℚ_[p] => φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ))
        {g : ℚ_[p] | g ≠ 0} μ ∧
    Summable (fun k : ℕ => primePowerTraceTerm φ (⟨p, hp.out⟩, k)) ∧
    ((Real.log p / μ.real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
        ∫ g in {g : ℚ_[p] | g ≠ 0},
          φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂μ =
      ∑' k : ℕ, primePowerTraceTerm φ (⟨p, hp.out⟩, k) := by sorry

end MasulloAudit
