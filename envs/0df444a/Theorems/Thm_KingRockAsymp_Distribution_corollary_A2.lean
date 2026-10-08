-- Prove2me | Theorems.Thm_KingRockAsymp_Distribution_corollary_A2
-- name    : KingRockAsymp.Distribution.corollary_A2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:06:58.933491+00:00
-- url     : https://prove2.me/theorems/4e8fbcb1-bb0d-45bc-9416-4c5ef7b00677
-- title:
--   Corollary A2 — the empirical mean $\bar f^\nu$ is a $C_m(U)$-valued random variable
-- statement:
--   Let $U \subseteq \mathbb R^n$ be compact, let $f : U \times S \to \mathbb R^m$ and the samples $s_1, s_2, \dots$ satisfy P.1–P.4, and let each $s_i$ be measurable. Then for every positive $\nu$ the empirical mean
--   $$\bar f^\nu = \frac1\nu \sum_{i=1}^\nu f(\cdot, s_i)$$
--   is a random variable with values in $C_m(U)$, i.e. a Borel measurable map from the sample space into $C_m(U)$.
--
--   This is what makes the convergence in distribution of $\sqrt\nu(\bar f^\nu - Ef)$ in Theorem A3 meaningful.
--
--   **Formalization Note** The sum runs over $i = 0, \dots, \nu - 1$ (`Finset.range ν`), i.e. $s_{i+1}$ is `s i`. The corollary requires $\nu \ge 1$, where the paper defines the sample mean. P.1–P.4 are inherited from the Appendix's standing assumptions.
-- source:
--   King & Rockafellar, Asymptotic Theory for Solutions in Statistical Estimation and Stochastic Programming, Math. Oper. Res. 18(1) (1993), Appendix, Corollary A2, p. 16 (authors' manuscript pagination)

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic

namespace KingRockAsymp.Distribution

open Set Filter Topology Metric MeasureTheory ProbabilityTheory

theorem corollary_A2 {n m : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set (Rn n)) [CompactSpace ↥U] (f : S → C(↥U, Rn m))
    (hmeas : ∀ x : ↥U, Measurable (fun σ => f σ x))
    (s : ℕ → Ω → S) (hs : ∀ i, Measurable (s i))
    (hindep : iIndepFun s P) (hident : ∀ i, IdentDistrib (s i) (s 0) P P)
    (hP3 : ∃ x : ↥U, MemLp (fun ω => f (s 0 ω) x) 2 P)
    (hP4 : ∃ a : S → ℝ, MemLp (fun ω => a (s 0 ω)) 2 P ∧
      ∀ σ : S, ∀ x₁ x₂ : ↥U, ‖f σ x₁ - f σ x₂‖ ≤ a σ * ‖(x₁ : Rn n) - x₂‖) :
    ∀ ν : ℕ, 1 ≤ ν →
      Measurable (fun ω => (ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f (s i ω)) := by sorry

end KingRockAsymp.Distribution
