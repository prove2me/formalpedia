-- Prove2me | Theorems.Thm_MultiItemRev_TwoIID_lemma_19
-- name    : MultiItemRev.TwoIID.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:30:48.586741+00:00
-- url     : https://prove2.me/theorems/d72d44fb-cabb-4022-8012-d82e81582254
-- title:
--   Lemma 19, p. 35 — revenue bounded at a lower valuation
-- statement:
--   Suppose a one-good valuation $X$ is at least $x_0\ge0$ almost surely. For every feasible, incentive-compatible and individually rational mechanism $\mu=(q,s)$,
--
--   $$R(\mu;X)\le(1-q(x_0))\operatorname{Rev}_1(X)+s(x_0).$$
--
--   The lemma bounds the payment of a mechanism by its allocation and payment at the lower endpoint, and is applied to conditional one-good valuations in Theorem B.
--
--   **Formalization Note** The individual mechanism's revenue is extended real, so negative expected payments are retained. The optimal revenue may be infinite; extended-real multiplication gives $0\cdot\infty=0$ in the case $q(x_0)=1$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 35, Lemma 19 (14)

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.TwoIID

theorem lemma_19 (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (x₀ : ℝ≥0) (hx₀ : ν {t | t < x₀} = 0)
    (M : MultiItemRev.Decomp.Mechanism Unit) (hM : IsAdmissible M) :
    expRevenue (MultiItemRev.Decomp.oneGood ν) M ≤
      ((1 - M.q (fun _ => x₀) () : ℝ) : EReal) * (MultiItemRev.Decomp.Rev1 ν : EReal) +
        (M.s (fun _ => x₀) : EReal) := by sorry

end MultiItemRev.TwoIID
