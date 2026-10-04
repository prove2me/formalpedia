-- Prove2me | Theorems.Thm_MeanFieldOpt_NoOverlapGap_lemma_6_7
-- name    : MeanFieldOpt.NoOverlapGap.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:08:14.032737+00:00
-- url     : https://prove2.me/theorems/62830ec5-75ff-419c-a3e2-fd437b6b44f1
-- title:
--   Lemma 6.7 — $t\mapsto\mathbb E\{\partial_x^2\Phi(t,X_t)^2\}$ is continuous on $[0,1)$
-- statement:
--   Let $\xi$ be a mixture, $\gamma \in \mathscr L$, $\Phi = \Phi^\gamma$ the solution of the Parisi PDE with terminal condition $|x|$, and let $(X_t)_{t\in[0,1]}$ be the strong solution of the SDE (6.3) driven by a standard Brownian motion $(B_t)$. Then the function
--
--   $$t \mapsto \mathbb E\big\{ \partial_x^2 \Phi(t, X_t)^2 \big\}$$
--
--   is continuous on $[0,1)$.
--
--   This regularity allows one to pass from statements holding for almost every $t$ to statements holding for every $t$, as in the stationarity condition of Lemma 6.15.
--
--   **Formalization Note** $\partial_x^2\Phi(t,\cdot)$ is the iterated `deriv` of $\Phi^\gamma(t,\cdot)$, and the expectation is a Bochner integral; for $t < 1$ the integrand is bounded (the paper's Lemma 6.4), so the expectation is a genuine finite value. Time $t \in [0,1)$ indexes the process through $t \mapsto X_{t^+}$ with $t^+ = \max(t,0)$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 27, Lemma 6.7

import Mathlib
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Mixture
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Spaces
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Parisi
import Definitions.Def_MeanFieldOpt_NoOverlapGap_SDE

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace MeanFieldOpt.NoOverlapGap

/-- Lemma 6.7 (arXiv:2001.00904v1, p. 27): for `γ ∈ ℒ`, `t ↦ E{∂_x²Φ(t, X_t)²}` is continuous
on `[0, 1)`, where `X` solves the SDE (6.3) for `γ` driven by a Brownian motion `B`. -/
theorem lemma_6_7 (ξ : Mixture) (γ : ℝ → ℝ) (hγ : InL ξ γ)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B X : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B Pr) (hX : SolvesParisiSDE ξ γ Pr B X) :
    ContinuousOn
      (fun t : ℝ => ∫ ω, (deriv (deriv (fun y => PhiL ξ γ t y)) (X t.toNNReal ω)) ^ 2 ∂Pr)
      (Ico 0 1) := by sorry

end MeanFieldOpt.NoOverlapGap
