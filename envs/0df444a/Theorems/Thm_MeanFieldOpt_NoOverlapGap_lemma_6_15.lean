-- Prove2me | Theorems.Thm_MeanFieldOpt_NoOverlapGap_lemma_6_15
-- name    : MeanFieldOpt.NoOverlapGap.lemma_6_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:08:33.928053+00:00
-- url     : https://prove2.me/theorems/04a19c15-8b03-4572-b8cd-77fff8f9ad1b
-- title:
--   Lemma 6.15 — stationarity $\mathbb E\{\partial_x\Phi^{\gamma_*}(t,X_t)^2\}=t$ under no overlap gap
-- statement:
--   Let $\xi$ be a mixture that is not identically zero. Assume the **no-overlap gap assumption** (Assumption 2): there is $\gamma_* \in \mathscr U$, strictly increasing on $[0,1)$, such that
--
--   $$\mathsf P(\gamma_*) = \inf_{\gamma \in \mathscr U} \mathsf P(\gamma).$$
--
--   Let $\Phi = \Phi^{\gamma_*}$ and let $(X_t)_{t\in[0,1]}$ be the solution of the SDE (6.3) for $\gamma_*$, driven by a standard Brownian motion. Then for every $t \in [0,1)$,
--
--   $$\mathbb E\big\{ \partial_x \Phi^{\gamma_*}(t, X_t)^2 \big\} = t .$$
--
--   This stationarity condition says that a strictly increasing minimiser over the monotone space $\mathscr U$ is a critical point of $\mathsf P$ in every admissible direction of the larger space $\mathscr L$.
--
--   **Formalization Note** The witness $\gamma_*$ is explicit, and minimality over $\mathscr U$ is stated as $\mathsf P(\gamma_*) \le \mathsf P(\gamma)$ for all $\gamma \in \mathscr U$ (attainment of the infimum). Strict monotonicity is required on $[0,1)$ only. The hypothesis that some coefficient $c_k$ is non-zero is not written in the lemma but is necessary: for $\xi \equiv 0$ every $\gamma$ minimises ($\mathsf P \equiv 0$), $X_t \equiv 0$, and the left side is constant in $t$; the paper's proof uses $\xi''(t) > 0$ on $(0,1)$, which holds exactly when $\xi \not\equiv 0$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 33, Lemma 6.15, Eq. (6.22); p. 8, Assumption 2

import Mathlib
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Mixture
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Spaces
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Parisi
import Definitions.Def_MeanFieldOpt_NoOverlapGap_SDE

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace MeanFieldOpt.NoOverlapGap

/-- Lemma 6.15 (arXiv:2001.00904v1, p. 33): under the no-overlap-gap assumption (Assumption 2,
p. 8), witnessed by a strictly increasing `γ_* ∈ 𝒰` minimizing `P` over `𝒰`, one has
`E{∂_xΦ^{γ_*}(t, X_t)²} = t` for every `t ∈ [0, 1)`, where `X` solves (6.3) for `γ_*`.
The hypothesis that the mixture is not identically zero is necessary (for `ξ ≡ 0` the
left side is constant in `t`). -/
theorem lemma_6_15 (ξ : Mixture) (hξ : ∃ k, ξ.c k ≠ 0)
    (γs : ℝ → ℝ) (hU : InU γs) (hsm : StrictMonoOn γs (Ico 0 1))
    (hmin : ∀ γ, InU γ → P ξ γs ≤ P ξ γ)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B X : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B Pr) (hX : SolvesParisiSDE ξ γs Pr B X) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      ∫ ω, (deriv (fun y => PhiL ξ γs t y) (X t.toNNReal ω)) ^ 2 ∂Pr = t := by sorry

end MeanFieldOpt.NoOverlapGap
