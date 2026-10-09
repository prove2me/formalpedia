-- Prove2me | Theorems.Thm_ModernOnlineLearning_Bandits_lemma_9_10
-- name    : ModernOnlineLearning.Bandits.lemma_9_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:38:29.340073+00:00
-- url     : https://prove2.me/theorems/ee8faf27-1b5e-44aa-8f43-c87bdebfa8b5
-- title:
--   Lemma 9.10, p. 160 — stochastic pseudo-regret is the sum of expected pulls times gaps
-- statement:
--   Fix a stochastic $d$-armed bandit with arm means $\mu_i$ and an optimal arm $j$, so $\mu_j\le\mu_i$ for all $i$. Let an online policy choose arm $A_t$ using only previously observed arms and losses, and write $S_{T,i}$ for its number of selections of arm $i$ through round $T$. If each new loss vector is independent of previous rounds and the current policy draw, then
--
--   $$\mathrm{P\!\operatorname{-}Regret}_T=\sum_{i=1}^{d}\mathbb E[S_{T,i}](\mu_i-\mu_j).$$
--
--   This identity turns a bound on suboptimal arm pulls into a pseudo-regret bound.
--
--   **Formalization Note** The loss vectors are independent across rounds. Measurability and integrability assumptions make each mean, expected loss, and expected pull count an ordinary real expectation. The policy is causal: $x_t$ is a measurable function of the arms and losses observed before round $t$. Arms use zero-based `Fin d` indices in Lean.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 9.10, p. 160

import Definitions.Def_ModernOnlineLearning_Bandits_Protocol
set_option autoImplicit false
noncomputable section

namespace ModernOnlineLearning.Bandits

/-- Orabona, Lemma 9.10, p. 160. Each arm's current loss is independent of
    the online policy's current choice because the policy sees only past losses. -/
theorem lemma_9_10 {Ω : Type*} [MeasurableSpace Ω]
    {T d : ℕ} (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (anchor : Fin d) (g : Ω → ℕ → Fin d → ℝ)
    (x : Ω → ArmPath T d → ℕ → Fin d → ℝ)
    (μ : Fin d → ℝ) (j : Fin d)
    (hPolicy : IsOnlinePolicy g x)
    (hIndep : ProbabilityTheory.iIndepFun (fun t : Fin T => fun ω => g ω (t.val + 1)) P)
    (hMeas : ∀ t i, Measurable (fun ω => g ω t i))
    (hLaw : ∀ t ∈ Finset.Icc 1 T, ∀ s ∈ Finset.Icc 1 T, ∀ i,
      P.map (fun ω => g ω t i) = P.map (fun ω => g ω s i))
    (hLossInt : ∀ t ∈ Finset.Icc 1 T, ∀ i,
      MeasureTheory.Integrable (fun ω => g ω t i) P)
    (hMean : ∀ t ∈ Finset.Icc 1 T, ∀ i, ∫ ω, g ω t i ∂P = μ i)
    (hInt : MeasureTheory.Integrable
      (fun ω => expectedLoss anchor (g ω) (x ω)) P)
    (hPullInt : ∀ i, MeasureTheory.Integrable
      (fun ω => expectedPullCount anchor (x ω) i) P)
    (hBest : ∀ i, μ j ≤ μ i) :
    stochasticPseudoRegret P anchor g x μ j =
      ∑ i, stochasticPullCount P anchor x i * gap μ j i := by sorry

end ModernOnlineLearning.Bandits
