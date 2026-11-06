-- Prove2me | Theorems.Thm_ImpatientQPTAS_lemma_2_5
-- name    : ImpatientQPTAS.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:45.410493+00:00
-- url     : https://prove2.me/theorems/8f0dac18-db8e-435c-8215-78ad44e8bbc7
-- title:
--   Lemma 2.5 — sequences of arbitrary length
-- statement:
--   Let $\epsilon\in(0,\tfrac14)$. For every customer $i\in C_{\mathrm{average}}$ and every real $\Delta\ge0$,
--   $$
--   (1-p^\uparrow_i)^{(1-\epsilon)\Delta}\ge(1-p^\downarrow_i)^\Delta .
--   $$
--
--   Over a long sequence the two probabilities are comparable once an $\epsilon$-fraction of the rounded-up sequence is cut, which is what the milestones of the coupling do.
--
--   Differences from the source: none.
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, Lemma 2.5, p.11; proof App. A.5

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Classes
import Definitions.Def_ImpatientQPTAS_Rounding

namespace ImpatientQPTAS

/-- Segev, arXiv:2209.13878v1, Lemma 2.5, p.11: for every customer `i ∈ C_average` and every `∆ ≥ 0`,
`(1 − p↑_i)^((1−ε)∆) ≥ (1 − p↓_i)^∆`.

**Formalization Note.** `∆` is real and the powers are `Real.rpow`: `(1−ε)∆` is not an integer. -/
theorem lemma_2_5 {n : ℕ} (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 4) (I : Instance n) (i : Fin n)
    (hi : i ∈ Caverage ε I) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    (1 - pDown ε (I.p i)) ^ Δ ≤ (1 - pUp ε (I.p i)) ^ ((1 - ε) * Δ) := by sorry

end ImpatientQPTAS
