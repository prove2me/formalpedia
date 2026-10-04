-- Prove2me | Theorems.Thm_MeanFieldOpt_NoOverlapGap_nog_minimizes_over_L
-- name    : MeanFieldOpt.NoOverlapGap.nog_minimizes_over_L
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:43:57.923247+00:00
-- url     : https://prove2.me/theorems/fd7f6507-4bf4-437e-b53b-1bd86f0dd7ab
-- title:
--   Section 6.3 — under no overlap gap, the monotone Parisi minimizer minimizes $\mathsf P$ over $\mathscr L$
-- statement:
--   Let $\xi$ be a mixture and let $\gamma_* \in \mathscr U$ be strictly increasing on $[0,1)$ and a minimiser of the Parisi functional over the monotone space:
--
--   $$\mathsf P(\gamma_*) = \inf_{\gamma \in \mathscr U} \mathsf P(\gamma).$$
--
--   Then $\gamma_*$ also minimises $\mathsf P$ over the larger space $\mathscr L$:
--
--   $$\mathsf P(\gamma_*) = \inf_{\gamma \in \mathscr L} \mathsf P(\gamma).$$
--
--   Since $\mathscr U \subseteq \mathscr L$, this gives $\inf_{\mathscr U} \mathsf P = \inf_{\mathscr L} \mathsf P$ under the no-overlap gap assumption: the paper's extended variational principle then reproduces the Parisi ground-state energy, which is how Corollary 2.2 obtains a $(1-\varepsilon)$-approximation algorithm.
--
--   **Formalization Note** Both minimalities are stated as attainment, $\mathsf P(\gamma_*) \le \mathsf P(\gamma)$ for all $\gamma$ in the respective space, never through a real infimum. The conclusion is about the given $\gamma_*$. No non-degeneracy hypothesis on $\xi$ is needed: for $\xi \equiv 0$, $\mathsf P \equiv 0$ on $\mathscr L$ and the claim holds.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 34, Section 6.3, first two paragraphs (the claim proving Corollary 2.2); p. 4, main result 2

import Mathlib
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Mixture
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Spaces
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Parisi

open MeasureTheory Set

namespace MeanFieldOpt.NoOverlapGap

/-- Section 6.3, the claim proving Corollary 2.2 (arXiv:2001.00904v1, p. 34): if `γ_* ∈ 𝒰` is
strictly increasing on `[0, 1)` and minimizes `P` over `𝒰`, then `γ_*` minimizes `P` over the
larger space `ℒ`. -/
theorem nog_minimizes_over_L (ξ : Mixture)
    (γs : ℝ → ℝ) (hU : InU γs) (hsm : StrictMonoOn γs (Ico 0 1))
    (hmin : ∀ γ, InU γ → P ξ γs ≤ P ξ γ) :
    ∀ γ, InL ξ γ → P ξ γs ≤ P ξ γ := by sorry

end MeanFieldOpt.NoOverlapGap
