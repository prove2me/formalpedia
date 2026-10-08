-- Prove2me | Theorems.Thm_MechanismDesign_DominantExamples_trade_dsic_iff
-- name    : MechanismDesign.DominantExamples.trade_dsic_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:30:43.282259+00:00
-- url     : https://prove2.me/theorems/63cb44d9-1995-4f1e-9e19-6eeaa312dc98
-- title:
--   Proposition 4.9 — dominant strategy IC trading mechanisms are threshold rules
-- statement:
--   A deterministic direct bilateral trade mechanism $(q, t_S, t_B)$ on $\Theta = [\underline\theta_S,\bar\theta_S]\times[\underline\theta_B,\bar\theta_B]$ is dominant strategy incentive-compatible if and only if the following two conditions hold.
--
--   1. For every $\theta_B \in [\underline\theta_B,\bar\theta_B]$ there are $\hat\theta_S \in \mathbb R$ and payments $\tau_S, \hat\tau_S \in \mathbb R$ such that for every $\theta_S \in [\underline\theta_S,\bar\theta_S]$: $\theta_S < \hat\theta_S \Rightarrow q(\theta) = 1$ and $t_S(\theta) = \hat\tau_S$; $\theta_S > \hat\theta_S \Rightarrow q(\theta) = 0$ and $t_S(\theta) = \tau_S$; $\theta_S = \hat\theta_S \Rightarrow$ either $q(\theta) = 0$ and $t_S(\theta) = \tau_S$, or $q(\theta) = 1$ and $t_S(\theta) = \hat\tau_S$; and
--   $$\hat\tau_S - \tau_S = \hat\theta_S.$$
--   2. For every $\theta_S \in [\underline\theta_S,\bar\theta_S]$ there are $\hat\theta_B \in \mathbb R$ and payments $\tau_B, \hat\tau_B \in \mathbb R$ such that for every $\theta_B \in [\underline\theta_B,\bar\theta_B]$: $\theta_B < \hat\theta_B \Rightarrow q(\theta) = 0$ and $t_B(\theta) = \tau_B$; $\theta_B > \hat\theta_B \Rightarrow q(\theta) = 1$ and $t_B(\theta) = \hat\tau_B$; $\theta_B = \hat\theta_B \Rightarrow$ either $q(\theta) = 0$ and $t_B(\theta) = \tau_B$, or $q(\theta) = 1$ and $t_B(\theta) = \hat\tau_B$; and
--   $$\hat\tau_B - \tau_B = \hat\theta_B.$$
--
--   Here $\theta = (\theta_S,\theta_B)$. The seller trades below her threshold and the buyer above his: the seller's orientation is reversed because high seller types are the least willing to sell.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.91, Proposition 4.9

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_BilateralTrade

namespace MechanismDesign.DominantExamples

/-- Proposition 4.9, p.91. A direct bilateral trade mechanism is dominant strategy
incentive-compatible if and only if
for every `θ_B ∈ [θ̲_B, θ̄_B]` there are a real number `θ̂_S` and payments `τ_S, τ̂_S ∈ ℝ`
such that for all `θ_S ∈ [θ̲_S, θ̄_S]`:
`θ_S < θ̂_S ⇒ q(θ) = 1 and t_S(θ) = τ̂_S`; `θ_S > θ̂_S ⇒ q(θ) = 0 and t_S(θ) = τ_S`;
`θ_S = θ̂_S ⇒ (q(θ) = 0 and t_S(θ) = τ_S) or (q(θ) = 1 and t_S(θ) = τ̂_S)`;
and `τ̂_S − τ_S = θ̂_S`;
and for every `θ_S ∈ [θ̲_S, θ̄_S]` there are a real number `θ̂_B` and payments
`τ_B, τ̂_B ∈ ℝ` such that for all `θ_B ∈ [θ̲_B, θ̄_B]`:
`θ_B < θ̂_B ⇒ q(θ) = 0 and t_B(θ) = τ_B`; `θ_B > θ̂_B ⇒ q(θ) = 1 and t_B(θ) = τ̂_B`;
`θ_B = θ̂_B ⇒ (q(θ) = 0 and t_B(θ) = τ_B) or (q(θ) = 1 and t_B(θ) = τ̂_B)`;
and `τ̂_B − τ_B = θ̂_B`. Here `θ = (θ_S, θ_B)`. -/
theorem trade_dsic_iff {E : TradeSetting} (M : TradeMechanism E) :
    M.IsDSIC ↔
      (∀ θB ∈ Set.Icc E.loB E.hiB, ∃ θhatS τS τhatS : ℝ,
        (∀ θS ∈ Set.Icc E.loS E.hiS, θS < θhatS →
          M.q (θS, θB) = 1 ∧ M.tS (θS, θB) = τhatS) ∧
        (∀ θS ∈ Set.Icc E.loS E.hiS, θhatS < θS →
          M.q (θS, θB) = 0 ∧ M.tS (θS, θB) = τS) ∧
        (∀ θS ∈ Set.Icc E.loS E.hiS, θS = θhatS →
          (M.q (θS, θB) = 0 ∧ M.tS (θS, θB) = τS) ∨
          (M.q (θS, θB) = 1 ∧ M.tS (θS, θB) = τhatS)) ∧
        τhatS - τS = θhatS) ∧
      (∀ θS ∈ Set.Icc E.loS E.hiS, ∃ θhatB τB τhatB : ℝ,
        (∀ θB ∈ Set.Icc E.loB E.hiB, θB < θhatB →
          M.q (θS, θB) = 0 ∧ M.tB (θS, θB) = τB) ∧
        (∀ θB ∈ Set.Icc E.loB E.hiB, θhatB < θB →
          M.q (θS, θB) = 1 ∧ M.tB (θS, θB) = τhatB) ∧
        (∀ θB ∈ Set.Icc E.loB E.hiB, θB = θhatB →
          (M.q (θS, θB) = 0 ∧ M.tB (θS, θB) = τB) ∨
          (M.q (θS, θB) = 1 ∧ M.tB (θS, θB) = τhatB)) ∧
        τhatB - τB = θhatB) := by sorry

end MechanismDesign.DominantExamples
