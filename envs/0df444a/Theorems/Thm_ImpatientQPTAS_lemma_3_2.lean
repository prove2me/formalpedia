-- Prove2me | Theorems.Thm_ImpatientQPTAS_lemma_3_2
-- name    : ImpatientQPTAS.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:02:56.380428+00:00
-- url     : https://prove2.me/theorems/68153846-331f-4b63-a72e-d8225badaf02
-- title:
--   Lemma 3.2 — $\mathcal Y^\downarrow\sim\mathcal X^\downarrow$
-- statement:
--   In the setting of §3, the variables $Y^\downarrow_{i,\tau}$, $i\in[n]$, $\tau\ge1$, are mutually independent, and each is Bernoulli with success probability $p^\downarrow_i$.
--
--   That is, $\mathcal Y^\downarrow$ has the law of the rounded-down process, so the coupling is valid.
--
--   Differences from the source:
--   - encoding: Y↓ ∼ X↓ → mutual independence of the family and the marginals; reason: this is the definition of X↓ on p.15
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, Lemma 3.2, p.18; definition of X↓, p.15

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Rounding
import Definitions.Def_ImpatientQPTAS_Coupling

namespace ImpatientQPTAS

open MeasureTheory ProbabilityTheory in
/-- Segev, arXiv:2209.13878v1, Lemma 3.2, p.18: `Y↓ ∼ X↓`, that is, the variables `Y↓_{i,τ}`, `τ ≥ 1`, are
mutually independent, each Bernoulli with success probability `p↓_i` (the definition of `X↓`, p.15). -/
theorem lemma_3_2 {n m γ : ℕ} {p : Fin n → ℝ} (hA : Admissible m γ p) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (C : Coupling m γ p P) :
    iIndepFun (fun q : Fin n × {τ : ℕ // 1 ≤ τ} => C.Ydown q.1 q.2.1) P ∧
      ∀ (i : Fin n) (τ : ℕ), 1 ≤ τ →
        P {ω | C.Ydown i τ ω = true} = ENNReal.ofReal (pDown (1 / (m : ℝ)) (p i)) := by sorry

end ImpatientQPTAS
