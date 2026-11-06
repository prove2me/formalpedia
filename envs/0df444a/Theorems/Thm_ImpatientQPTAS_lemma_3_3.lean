-- Prove2me | Theorems.Thm_ImpatientQPTAS_lemma_3_3
-- name    : ImpatientQPTAS.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:03:01.797662+00:00
-- url     : https://prove2.me/theorems/a7460eab-fe7e-419d-b951-74ae2f092fa9
-- title:
--   Lemma 3.3 — the served customer is available at the start of the block
-- statement:
--   In the setting of §3, let $S$ be an extended policy, $B$ a start set, $t\ge1$ a stage and $i$ a customer, and let $k$ be the milestone index with $\mu(t)\in[t_{k-1}+1,t_k-1]$. Almost surely, if $S(\mu(t),A^{\downarrow}_{\mu(t)})=i$, then
--   $$
--   i\in A^{\uparrow}_{\mu^{-1}(t_{k-1}+1)} .
--   $$
--
--   This is the first step towards showing that the rounded-up process can duplicate the actions of the simulated rounded-down one.
--
--   Differences from the source:
--   - reading: Pr[i ∈ A↑ | S(μ(t), A↓) = i] = 1 → the almost-sure implication; reason: the same statement with no undefined case when the conditioning event has probability 0
--   - generalization: the policy S*↓ from [n] → every extended policy S from every start set B; reason: the proof uses only that a policy serves an available customer
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, Lemma 3.3, p.22

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Rounding
import Definitions.Def_ImpatientQPTAS_Coupling

namespace ImpatientQPTAS

open MeasureTheory ProbabilityTheory in
/-- Segev, arXiv:2209.13878v1, Lemma 3.3, p.22: for every stage `t ≥ 1` and customer `i`,
`Pr[i ∈ A^{Y↑}_{μ⁻¹(t_{k−1}+1)} | S*↓(μ(t), A^{Y↓}_{μ(t)}) = i] = 1`, where `k` is the milestone index with
`μ(t) ∈ [t_{k−1} + 1, t_k − 1]`.

**Formalization Note.** Conditioning on a possibly null event is the almost-sure implication.
`lastMs (μ t)` is `t_{k−1}`, and `regCount` is `μ⁻¹` on the regular stage `t_{k−1} + 1`. The claim holds
for every extended policy `S` from every start set `B`, not only for `S*↓` from `[n]`. -/
theorem lemma_3_3 {n m γ : ℕ} {p : Fin n → ℝ} (hA : Admissible m γ p) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (C : Coupling m γ p P)
    (S : Policy n) (hS : IsExtPolicy S) (B : Finset (Fin n)) (t : ℕ) (ht : 1 ≤ t) (i : Fin n) :
    ∀ᵐ ω ∂P, C.simAction S B ω t = some i →
      i ∈ C.upSet S B ω (regCount m γ (lastMs m γ (mu m γ t) + 1)) := by sorry

end ImpatientQPTAS
