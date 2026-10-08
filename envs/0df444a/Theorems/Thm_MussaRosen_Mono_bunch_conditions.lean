-- Prove2me | Theorems.Thm_MussaRosen_Mono_bunch_conditions
-- name    : MussaRosen.Mono.bunch_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:33:12.358346+00:00
-- url     : https://prove2.me/theorems/fd526685-83e1-4145-bff7-0d3a768af84f
-- title:
--   (18)–(19), pp. 311, 314 — boundary conditions of an interior bunch
-- statement:
--   Under the standing hypotheses, let $q$ be an optimal assignment, and suppose it has an interior bunch at a positive quality: there are $\underline\theta<\theta^u<\theta^v<\bar\theta$ and $q^r>0$ with
--   1. $q(\theta)=q^r$ for $\theta^u\le\theta\le\theta^v$,
--   2. $\dot q(\theta)>0$ throughout some interval immediately to the left of $\theta^u$,
--   3. $\dot q(\theta)>0$ throughout some interval immediately to the right of $\theta^v$.
--
--   Then
--   $$C'(q^r)=MR(\theta^u),\qquad C'(q^r)=MR(\theta^v),\qquad \int_{\theta^u}^{\theta^v}\bigl[MR(\theta)-C'(q^r)\bigr]f(\theta)\,d\theta=0 .$$
--   The first two equalities are (18), $G(\theta^u)=q^r=G(\theta^v)$; the third is (19), $\mu(\theta^u)-\mu(\theta^v)=0$. Equivalently, the average marginal revenue over the bunch, $\frac{1}{F(\theta^v)-F(\theta^u)}\int_{\theta^u}^{\theta^v}MR(\theta)f(\theta)\,d\theta$, equals the marginal cost $C'(q^r)$.
--
--   These conditions determine the bunch when marginal revenue is not monotone.
--
--   **Formalization Note** Hypotheses 2 and 3 state explicitly the paper's condition that the neighboring intervals have $\dot q>0$. (18) is written through $C'$ instead of $G$.
-- source:
--   Mussa and Rosen, Monopoly and product quality, J. Econ. Theory 18 (1978), p. 311, §4, case (ii); p. 314, §5, equations (18), (19)

import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem bunch_conditions {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q)
    (θu θv qr : ℝ) (hlo : θlo < θu) (huv : θu < θv) (hhi : θv < θhi) (hqr : 0 < qr)
    (hflat : ∀ θ ∈ Set.Icc θu θv, q θ = qr)
    (hleft : ∃ a : ℝ, θlo ≤ a ∧ a < θu ∧
      ∀ θ ∈ Set.Ioo a θu, ∃ d : ℝ, 0 < d ∧ HasDerivAt q d θ)
    (hright : ∃ b : ℝ, θv < b ∧ b ≤ θhi ∧
      ∀ θ ∈ Set.Ioo θv b, ∃ d : ℝ, 0 < d ∧ HasDerivAt q d θ) :
    deriv C qr = virtualValuation D θu ∧ deriv C qr = virtualValuation D θv ∧
      ∫ θ in θu..θv, (virtualValuation D θ - deriv C qr) * D.f θ = 0 := by sorry

end MussaRosen.Mono
