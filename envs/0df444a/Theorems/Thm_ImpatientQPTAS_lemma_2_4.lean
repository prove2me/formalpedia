-- Prove2me | Theorems.Thm_ImpatientQPTAS_lemma_2_4
-- name    : ImpatientQPTAS.lemma_2_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T21:01:58.473319+00:00
-- url     : https://prove2.me/theorems/e8bd3899-3d9a-4688-988a-e77da519e9e3
-- title:
--   Lemma 2.4 — short sequences of stages
-- statement:
--   Let $\epsilon\in(0,\tfrac14)$. For every customer $i\in C_{\mathrm{average}}$ and every real $\Delta\in[0,1/\epsilon)$,
--   $$
--   (1-p^\uparrow_i)^\Delta\ge(1-\epsilon)\,(1-p^\downarrow_i)^\Delta .
--   $$
--
--   Over fewer than $1/\epsilon$ stages, a customer's chance of not departing barely changes between the two roundings.
--
--   Differences from the source: none.
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, Lemma 2.4, p.11; proof App. A.4

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Classes
import Definitions.Def_ImpatientQPTAS_Rounding

namespace ImpatientQPTAS

/-- Segev, arXiv:2209.13878v1, Lemma 2.4, p.11: for every customer `i ∈ C_average` and every
`∆ ∈ [0, 1/ε)`, `(1 − p↑_i)^∆ ≥ (1 − ε)·(1 − p↓_i)^∆`.

**Formalization Note.** `∆` is real and the powers are `Real.rpow`, on bases in `(0, 1)`. -/
theorem lemma_2_4 {n : ℕ} (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 4) (I : Instance n) (i : Fin n)
    (hi : i ∈ Caverage ε I) (Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ < 1 / ε) :
    (1 - ε) * (1 - pDown ε (I.p i)) ^ Δ ≤ (1 - pUp ε (I.p i)) ^ Δ := by sorry

end ImpatientQPTAS
