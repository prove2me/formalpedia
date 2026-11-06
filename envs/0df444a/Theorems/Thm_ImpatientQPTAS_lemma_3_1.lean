-- Prove2me | Theorems.Thm_ImpatientQPTAS_lemma_3_1
-- name    : ImpatientQPTAS.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:02:54.910332+00:00
-- url     : https://prove2.me/theorems/f6aad26b-23b0-4cf6-a4c5-73217fafb382
-- title:
--   Lemma 3.1 — the coupling is non-anticipative
-- statement:
--   In the setting of §3, for every stage $\tau\ge1$, the history $\mathcal Y^{\downarrow\le\tau}$ is a deterministic function of
--   $$
--   (\mathcal Z^{\le\tau},\mathcal W^{\le\tau},\mathcal V^{\le\tau},\mathcal Y^{\uparrow\le\mu^{-1}(\tau)})\ \text{ if }\tau\notin M_\gamma,\qquad
--   (\mathcal Z^{\le\tau},\mathcal W^{\le\tau},\mathcal V^{\le\tau},\mathcal Y^{\uparrow\le\mu^{-1}(\tau-1)})\ \text{ if }\tau\in M_\gamma .
--   $$
--   In particular, $\mathcal Y^{\downarrow\le\tau}$ is independent of all the coins beyond these.
--
--   The rounded-down process thus uses no future information about the rounded-up process.
--
--   **Formalization Note** At $\tau=1\in M_\gamma$ (that is, $\gamma=1$) the history of $\mathcal Y^\uparrow$ is empty.
--
--   Differences from the source:
--   - encoding: two mappings ν₁, ν₂, for regular stages and milestones → one map ν, on the coins of Coin.Past; reason: regCount τ equals μ⁻¹(τ) on a regular stage and μ⁻¹(τ − 1) on a milestone, so the two cases are one
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, Lemma 3.1, p.18; proof App. A.7, p.35

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Rounding
import Definitions.Def_ImpatientQPTAS_Coupling

namespace ImpatientQPTAS

open MeasureTheory ProbabilityTheory in
/-- Segev, arXiv:2209.13878v1, Lemma 3.1, p.18: `Y↓^{≤τ}` is a deterministic function of
`(Z^{≤τ}, W^{≤τ}, V^{≤τ}, Y↑^{≤μ⁻¹(τ)})` for regular `τ`, and of
`(Z^{≤τ}, W^{≤τ}, V^{≤τ}, Y↑^{≤μ⁻¹(τ−1)})` for a milestone `τ`; in particular it is independent of the
coins beyond them.

**Formalization Note.** `Coin.Past` covers both cases at once, through `regCount`, which equals `μ⁻¹(τ)`
on a regular stage and `μ⁻¹(τ − 1)` on a milestone. At `τ = 1 ∈ M_γ` (`γ = 1`) that history of `Y↑` is
empty. `ν` is one map for both of the printed `ν₁`, `ν₂`. -/
theorem lemma_3_1 {n m γ : ℕ} {p : Fin n → ℝ} (hA : Admissible m γ p) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (C : Coupling m γ p P) (τ : ℕ)
    (hτ : 1 ≤ τ) :
    (∃ ν : ({c : Coin n // c.Valid m γ ∧ c.Past m γ τ} → Bool) → Fin n → ℕ → Bool,
      ∀ (ω : Ω) (i : Fin n) (s : ℕ), 1 ≤ s → s ≤ τ →
        C.Ydown i s ω = ν (fun c => C.coin c.1 ω) i s) ∧
    IndepFun (fun (ω : Ω) (q : Fin n × {s : ℕ // 1 ≤ s ∧ s ≤ τ}) => C.Ydown q.1 q.2.1 ω)
      (fun (ω : Ω) (c : {c : Coin n // c.Valid m γ ∧ ¬ c.Past m γ τ}) => C.coin c.1 ω) P := by sorry

end ImpatientQPTAS
