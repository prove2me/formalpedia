-- Prove2me | Theorems.Thm_MussaRosen_Mono_virtualValuation_lt_self
-- name    : MussaRosen.Mono.virtualValuation_lt_self
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:11:42.388839+00:00
-- url     : https://prove2.me/theorems/749e89c7-b632-4e55-864b-114c9ee43a7f
-- title:
--   §4, p. 308 — marginal revenue MR(θ) is below θ except at θ = θ̄
-- statement:
--   Let $f$ be a density on $[\underline\theta,\bar\theta]$, positive on the whole interval, with distribution function $F(\theta)=\int_{\underline\theta}^\theta f(s)\,ds$, and let
--   $$MR(\theta)=\theta-\frac{1-F(\theta)}{f(\theta)}$$
--   be the marginal revenue of (8). Then
--   $$MR(\theta)<\theta\quad\text{for }\underline\theta\le\theta<\bar\theta,\qquad MR(\bar\theta)=\bar\theta .$$
--
--   The gap between marginal revenue and the incremental demand price $\theta$ is what drives the monopolist to restrict quality; equality at the top type is why the top type is undistorted.
-- source:
--   Mussa and Rosen, Monopoly and product quality, J. Econ. Theory 18 (1978), p. 308, §4, second paragraph (from (8))

import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem virtualValuation_lt_self {θlo θhi : ℝ} (D : TypeDistribution θlo θhi) :
    (∀ θ ∈ Set.Ico θlo θhi, virtualValuation D θ < θ) ∧ virtualValuation D θhi = θhi := by sorry

end MussaRosen.Mono
