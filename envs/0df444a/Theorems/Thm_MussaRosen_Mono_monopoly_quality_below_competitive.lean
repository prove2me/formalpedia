-- Prove2me | Theorems.Thm_MussaRosen_Mono_monopoly_quality_below_competitive
-- name    : MussaRosen.Mono.monopoly_quality_below_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:36:00.493002+00:00
-- url     : https://prove2.me/theorems/925822a2-608d-49da-b3fd-e77fa04cb534
-- title:
--   §4 p. 312 and §6 'First' pp. 314–315 — an optimal monopoly assignment is below the competitive one except at the top
-- statement:
--   **Setting.** Consumer types $\theta$ are distributed on $[\underline\theta,\bar\theta]$ ($0\le\underline\theta<\bar\theta$) with a density $f$ that is positive and differentiable on the whole interval; $F(\theta)=\int_{\underline\theta}^\theta f$ and $MR(\theta)=\theta-(1-F(\theta))/f(\theta)$. The unit cost $C$ of quality satisfies $C(0)=0$, is twice differentiable, and $C'(q)>0$, $C''(q)>0$ for all $q\ge0$. Under competition type $\theta$ buys the quality $J(\theta)$ with $C'(J(\theta))=\theta$ when $\theta>C'(0)$, and does not buy when $\theta\le C'(0)$. Let $q$ be an optimal monopoly assignment: nondecreasing, nonnegative and piecewise differentiable on $[\underline\theta,\bar\theta]$, maximizing
--   $$\Pi(q)=\int_{\underline\theta}^{\bar\theta}\Bigl[\theta\,q(\theta)-\int_{\underline\theta}^{\theta}q(s)\,ds-C(q(\theta))\Bigr]f(\theta)\,d\theta$$
--   among all such assignments.
--
--   **Claim.** Then
--   1. every type served under competition, other than the top type, gets a strictly lower quality from the monopolist:
--   $$C'(q(\theta))<\theta\quad\text{for all }\underline\theta\le\theta<\bar\theta\text{ with }\theta>C'(0),$$
--   that is, $q^m(\theta)<q^c(\theta)=J(\theta)$ wherever $J(\theta)>0$;
--   2. types not served under competition are not served by the monopolist: $q(\theta)=0$ for $\underline\theta\le\theta<\bar\theta$ with $\theta\le C'(0)$;
--   3. the top type gets the competitive quality: if $C'(0)<\bar\theta$, then $q(\theta)$ converges, as $\theta\uparrow\bar\theta$, to a limit $L$ with $C'(L)=\bar\theta$, i.e. $q^m(\bar\theta)=J(\bar\theta)$; if $\bar\theta\le C'(0)$, then $q(\theta)\to0$.
--
--   This is the paper's main conclusion: the monopolist lowers the quality sold to every consumer who buys under competition, except the consumer with the highest valuation of quality ("no distortion at the top").
--
--   **Formalization Note** The competitive assignment $J=C'^{-1}$ is never formed: "$q(\theta)<J(\theta)$" is written as $C'(q(\theta))<\theta$, which is equivalent because $C'$ is strictly increasing on $q\ge0$. The value at the top is stated as a left limit, because the profit integral does not depend on the single value $q(\bar\theta)$, which an optimal assignment may raise freely. The paper writes "$MR(\bar\theta)=\bar\theta=J(\bar\theta)$" on p. 312; the intended reading is $MR(\bar\theta)=\bar\theta$, hence $G(\bar\theta)=J(\bar\theta)$. $C(0)=0$ encodes that quality $0$ means not buying, so that no cost is charged for unserved types.
-- source:
--   Mussa and Rosen, Monopoly and product quality, J. Econ. Theory 18 (1978), p. 312 (§4, paragraph 'These conditions imply …') and pp. 314–315 (§6, 'First')

import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem monopoly_quality_below_competitive {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q) :
    (∀ θ ∈ Set.Ico θlo θhi, deriv C 0 < θ → deriv C (q θ) < θ) ∧
    (∀ θ ∈ Set.Ico θlo θhi, θ ≤ deriv C 0 → q θ = 0) ∧
    ((deriv C 0 < θhi → ∃ L : ℝ, Tendsto q (𝓝[<] θhi) (𝓝 L) ∧ deriv C L = θhi) ∧
      (θhi ≤ deriv C 0 → Tendsto q (𝓝[<] θhi) (𝓝 0))) := by sorry

end MussaRosen.Mono
