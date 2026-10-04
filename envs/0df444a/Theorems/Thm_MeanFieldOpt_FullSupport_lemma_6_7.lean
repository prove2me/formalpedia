-- Prove2me | Theorems.Thm_MeanFieldOpt_FullSupport_lemma_6_7
-- name    : MeanFieldOpt.FullSupport.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:10:28.5386+00:00
-- url     : https://prove2.me/theorems/b26c0f3f-a3b3-483e-8830-33aaa7f78cc5
-- title:
--   Lemma 6.7 — $t\mapsto\mathbb E\{\partial_x^2\Phi(t,X_t)^2\}$ is continuous on $[0,1)$
-- statement:
--   Let $\xi$ be a mixture, $f_0$ an admissible terminal condition, $\gamma \in \mathscr L$, $\Phi = \Phi^\gamma$, and let $X$ be the strong solution of the SDE (6.3) driven by a standard Brownian motion. Then the function
--
--   $$
--   t \longmapsto \mathbb E\{\partial_x^2\Phi(t, X_t)^2\}
--   $$
--
--   is continuous on $[0,1)$.
--
--   Continuity upgrades the almost-everywhere identities obtained from the first variation of the Parisi functional to identities at every point of the support.
--
--   **Formalization Note** $\partial_x^2\Phi$ is the second iterated `deriv` in $x$; the expectation is a Bochner integral over the probability space. The statement holds for every strong solution $X$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 27, Lemma 6.7

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_IsTerminal
import Definitions.Def_MeanFieldOpt_FullSupport_InL
import Definitions.Def_MeanFieldOpt_FullSupport_ParisiSDE

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MeanFieldOpt.FullSupport

/-- Lemma 6.7 (arXiv:2001.00904v1, p. 27): for `γ ∈ ℒ`, the function
`t ↦ E{∂²_xΦ(t, X_t)²}` is continuous on `[0,1)`. -/
theorem lemma_6_7 (ξ : Mixture) (f₀ : ℝ → ℝ) (hf₀ : IsTerminal f₀) (γ : ℝ → ℝ)
    (hγ : InL ξ γ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W X : ℝ≥0 → Ω → EthierKurtz.SDEState 1) (hW : IsBrownianReal (fun t ω => W t ω 0) P)
    (hX : IsParisiSDESol ξ f₀ γ P W X) :
    ContinuousOn (fun t => ∫ ω, (deriv (deriv (PhiL ξ f₀ γ t)) (pathAt X t ω)) ^ 2 ∂P)
      (Set.Ico 0 1) := by sorry

end MeanFieldOpt.FullSupport
