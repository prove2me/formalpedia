-- Prove2me | Theorems.Thm_ImpatientQPTAS_lemma_3_4
-- name    : ImpatientQPTAS.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:03:15.377271+00:00
-- url     : https://prove2.me/theorems/0244f0a5-c0a1-44fd-8532-4c43153f0067
-- title:
--   Lemma 3.4 — the served customer is available at stage $t$
-- statement:
--   In the setting of §3, with $\epsilon=1/m$, let $S$ be an extended policy, $B$ a start set, $t\ge1$ a stage and $i$ a customer, and let $E$ be the event $\{S(\mu(t),A^\downarrow_{\mu(t)})=i\}$. Then
--   $$
--   \Pr\big[E\cap\{i\in A^{\uparrow}_t\}\big]\ge(1-\epsilon)\Pr[E].
--   $$
--
--   So the policy of eq. (10) implements the decision of the simulated process with conditional probability at least $1-\epsilon$.
--
--   **Formalization Note** In the printed (15)–(16) the exponent and the instantiation of Lemma 2.4 must use the block length $\Delta=\mu(t)-t_{k-1}-1\le 1/\epsilon-2$, not $t-t_{k-1}-1$; the lemma is unaffected.
--
--   Differences from the source:
--   - reading: Pr[i ∈ A↑_t | E] ≥ 1 − ε → P(E ∩ {i ∈ A↑_t}) ≥ (1 − ε)·P(E); reason: the same statement with no undefined case when P(E) = 0
--   - generalization: the policy S*↓ from [n] → every extended policy S from every start set B; reason: the proof uses only that a policy serves an available customer
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, Lemma 3.4, p.23; (15)–(16), p.24

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Rounding
import Definitions.Def_ImpatientQPTAS_Coupling

namespace ImpatientQPTAS

open MeasureTheory ProbabilityTheory in
/-- Segev, arXiv:2209.13878v1, Lemma 3.4, p.23: for every stage `t ≥ 1` and customer `i`,
`Pr[i ∈ A^{Y↑}_t | S*↓(μ(t), A^{Y↓}_{μ(t)}) = i] ≥ 1 − ε`.

**Formalization Note.** With `E` the conditioning event, the statement is
`P(E ∩ {i ∈ A^{Y↑}_t}) ≥ (1 − ε)·P(E)`, which has no undefined case when `P(E) = 0`. It holds for every
extended policy `S` from every start set `B`. -/
theorem lemma_3_4 {n m γ : ℕ} {p : Fin n → ℝ} (hA : Admissible m γ p) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (C : Coupling m γ p P)
    (S : Policy n) (hS : IsExtPolicy S) (B : Finset (Fin n)) (t : ℕ) (ht : 1 ≤ t) (i : Fin n) :
    (1 - 1 / (m : ℝ)) * P.real {ω | C.simAction S B ω t = some i} ≤
      P.real {ω | C.simAction S B ω t = some i ∧ i ∈ C.upSet S B ω t} := by sorry

end ImpatientQPTAS
