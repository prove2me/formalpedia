-- Prove2me | Theorems.Thm_MasulloRH_dyadic_profile_log_integral_and_divergence
-- name    : MasulloRH.dyadic_profile_log_integral_and_divergence
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T01:25:43.203992+00:00
-- url     : https://prove2.me/theorems/ad1ce3d4-fe43-47d0-9a73-d0c15309bc13
-- title:
--   Logarithmic integral and divergence of the dyadic sieve profile
-- statement:
--   Let $b:\mathbb R\to\mathbb R$ be continuous and let $G:\mathbb R\to\mathbb R$ satisfy
--   $$G(t)=\tfrac12 b(2^{k+1}t)\qquad(2^{-k-1}\le t\le2^{-k},\ k=0,1,2,\ldots).$$
--   Write $I=\int_1^2 b(u)\,du/u$. Then for every integer $m\ge0$,
--   $$\int_{2^{-m}}^1 G(t)\,\frac{dt}{t}=\frac m2 I.$$
--   If $I>0$, these truncated integrals tend to $+\infty$ and $G(t)/t$ is not Lebesgue integrable on $(0,1]$. The dyadic identity is the hypothesis needed when applying the result to a limiting sieve profile.
-- source:
--   Direct change of scale and interval additivity for a candidate dyadic limiting profile in the Masullo RH mission. The conditional statement isolates the continuous integral once the dyadic piece formula for the sieve has been established. Related mission: https://prove2.me/missions/Masullo%3A_The_Music_of_the_Primes_%E2%80%94_Riemann_Hypothesis_specialization .

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter MeasureTheory Set
open scoped Topology

theorem MasulloRH.dyadic_profile_log_integral_and_divergence (b G : ℝ → ℝ) (hb : Continuous b)
    (hpiece : ∀ k : ℕ, ∀ t ∈ Icc ((1/2:ℝ)^(k+1)) ((1/2:ℝ)^k),
      G t = (1/2:ℝ)*b ((2:ℝ)^(k+1)*t)) :
    (∀ m : ℕ, (∫ t in (1/2:ℝ)^m..1, G t/t) = (m:ℝ)/2 * ∫ u in (1:ℝ)..2, b u/u) ∧
    (0 < (∫ u in (1:ℝ)..2, b u/u) →
      Tendsto (fun m : ℕ => ∫ t in (1/2:ℝ)^m..1, G t/t) atTop atTop ∧
      ¬ IntegrableOn (fun t : ℝ => G t/t) (Ioc 0 1)) := by sorry
