-- Prove2me | Theorems.Thm_MussaRosen_Mono_mu_nonpos
-- name    : MussaRosen.Mono.mu_nonpos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:14:48.740073+00:00
-- url     : https://prove2.me/theorems/fcf87400-393b-42a1-b9fd-fd42e4e5a1c2
-- title:
--   (13), p. 309 — μ(θ) ≤ 0 for all θ at an optimum
-- statement:
--   Under the standing hypotheses (positive differentiable density $f$ on $[\underline\theta,\bar\theta]$; $C(0)=0$, $C$ twice differentiable, $C'>0$ and $C''>0$ on $q\ge0$), let $q$ be an optimal assignment and let $\mu$ be the marginal profit of (10). Then
--   $$\mu(t)\le 0\qquad\text{for all }t\in[\underline\theta,\bar\theta].$$
--
--   It says that no uniform increase of quality for all types above a threshold raises profit.
-- source:
--   Mussa and Rosen, Monopoly and product quality, J. Econ. Theory 18 (1978), p. 309, §4, condition (13)

import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem mu_nonpos {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q) :
    ∀ t ∈ Set.Icc θlo θhi, mu D C q t ≤ 0 := by sorry

end MussaRosen.Mono
