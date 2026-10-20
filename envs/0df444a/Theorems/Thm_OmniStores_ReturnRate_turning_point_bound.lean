-- Prove2me | Theorems.Thm_OmniStores_ReturnRate_turning_point_bound
-- name    : OmniStores.ReturnRate.turning_point_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:11.216121+00:00
-- url     : https://prove2.me/theorems/071e78a2-9edd-4e86-ac59-65c01ea7ad78
-- title:
--   Proof of Lemma 1, OA p. 1 — the zero-or-turning-point profit bound
-- statement:
--   Fix an assortment $S$, a return rate $0<\gamma<1$, and any store count $n\geq0$. Under the standing assumptions, its profit is bounded by the larger of the online-only profit and the profit at the positive-store turning point:
--
--   $$\pi(\gamma,n,S)\leq\max\{\pi(\gamma,0,\varnothing),\ \pi(\gamma,n^*(\gamma),S)\}.$$
--
--   This is the endpoint comparison behind Lemma 1's store-count selection.
--
--   **Formalization Note.** The source says an optimal $n$ “must be” either endpoint. At a threshold tie, intermediate counts can also be optimal, so the inequality states the valid optimization claim without excluding those ties.
-- source:
--   Gao, Agrawal & Cui, “The Effect of Multi-Channel and Omni-Channel Retailing on Physical Stores”, authors' manuscript (PDF of 2020-12-25), proof of Lemma 1, Online Appendix p. 1 (PDF p. 34)

import Definitions.Def_OmniStores_ReturnRate_ClosedForms

namespace OmniStores.ReturnRate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Proof of Lemma 1, Online Appendix p. 1: the maximum over the store count
for each fixed assortment is attained at zero or the positive turning point.
The inequality records the valid envelope when the two endpoints tie. -/
theorem turning_point_bound (P : Params ι) (hP : P.Standing)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (n : ℝ) (S : Finset ι)
    (hn : 0 ≤ n) :
    profit P γ n S ≤ max (profit P γ 0 ∅) (profit P γ (nStar P γ) S) := by sorry

end OmniStores.ReturnRate
