-- Prove2me | Theorems.Thm_MeanFieldOpt_FullSupport_lemma_6_9
-- name    : MeanFieldOpt.FullSupport.lemma_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:30:35.079357+00:00
-- url     : https://prove2.me/theorems/075c6042-ebbf-4cdf-9cc4-1ce60761d4f2
-- title:
--   Lemma 6.9 — $S(\gamma)$ is a countable disjoint union of intervals $(a,b)$ or $[a,b)$
-- statement:
--   Let $\xi$ be a mixture and let $\gamma \in \mathscr L$ be right-continuous on $[0,1)$ (the paper's standing convention from p. 28 on). Then the support $S(\gamma) = \{t \in [0,1) : \gamma(t) > 0\}$ is a disjoint union of countably many intervals
--
--   $$
--   S(\gamma) = \bigcup_{\alpha \in A} I_\alpha, \qquad I_\alpha = (a_\alpha, b_\alpha) \ \text{ or } \ I_\alpha = [a_\alpha, b_\alpha), \quad a_\alpha < b_\alpha,
--   $$
--
--   with $A$ countable.
--
--   The structure of the support is what lets the stationarity conditions be applied interval by interval in the proof of the main theorem.
--
--   **Formalization Note** The index set is a countable set of triples $(a, b, \text{flag})$, the flag selecting $[a,b)$ (`true`) or $(a,b)$ (`false`); the intervals are pairwise disjoint. Right-continuity is `ContinuousWithinAt γ (Set.Ici t) t` for $t \in [0,1)$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 28, Lemma 6.9 (with the right-continuity convention stated just before it)

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_InL
import Definitions.Def_MeanFieldOpt_FullSupport_Support

namespace MeanFieldOpt.FullSupport

/-- Lemma 6.9 (arXiv:2001.00904v1, p. 28): for `γ ∈ ℒ` (right-continuous, the paper's convention
from p. 28), the support `S(γ)` is a disjoint union of countably many intervals
`I_α = (a_α, b_α)` or `I_α = [a_α, b_α)` with `a_α < b_α`. An index `(a, b, true)` stands for
`[a, b)` and `(a, b, false)` for `(a, b)`. -/
theorem lemma_6_9 (ξ : Mixture) (γ : ℝ → ℝ) (hγ : InL ξ γ)
    (hrc : ∀ t ∈ Set.Ico (0 : ℝ) 1, ContinuousWithinAt γ (Set.Ici t) t) :
    ∃ A : Set (ℝ × ℝ × Bool), A.Countable ∧ (∀ α ∈ A, α.1 < α.2.1) ∧
      A.PairwiseDisjoint
        (fun α => if α.2.2 then Set.Ico α.1 α.2.1 else Set.Ioo α.1 α.2.1) ∧
      S γ = ⋃ α ∈ A, (if α.2.2 then Set.Ico α.1 α.2.1 else Set.Ioo α.1 α.2.1) := by sorry

end MeanFieldOpt.FullSupport
