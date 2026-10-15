-- Prove2me | Theorems.Thm_FreeSamples_Revenue_lemma_1_i
-- name    : FreeSamples.Revenue.lemma_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:49.737989+00:00
-- url     : https://prove2.me/theorems/acc35ca9-1435-4329-8454-bf82f305f099
-- title:
--   Lemma 1(i), p. 14 — the Buyer's posterior variance decreases at rate σ_t⁴/σ²
-- statement:
--   Let $\sigma_t^2=\sigma_0^2\sigma^2/(\sigma_0^2t+\sigma^2)$ be the Buyer's posterior variance after $t$ samples, with $\sigma_0^2,\sigma^2>0$. For every $t\ge 0$, $t\mapsto\sigma_t^2$ has the right derivative
--   $$\frac{d}{dt}\sigma_t^2=-\frac{\sigma_t^4}{\sigma^2}.$$
--   The posterior variance is deterministic, so this is the statement $\mathbb E^B_t[d(\sigma_t^2)]=\mathbb E^S_t[d(\sigma_t^2)]=-\frac{\sigma_t^4}{\sigma^2}dt$ of Lemma 1(i), from both perspectives. It is the $\sigma^2$-direction of the drift of the Bayes risk in Lemma 4.
--
--   **Formalization Note.** The derivative is taken within $[t,\infty)$, which covers the one-sided derivative at $t=0$.
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, p. 14, Lemma 1(i)

import Mathlib
import Definitions.Def_FreeSamples_Revenue_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.Revenue

theorem lemma_1_i (p : Params) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => p.buyerVar s) (-(p.buyerVar t) ^ 2 / p.σsq) (Set.Ici t) t := by sorry

end FreeSamples.Revenue
