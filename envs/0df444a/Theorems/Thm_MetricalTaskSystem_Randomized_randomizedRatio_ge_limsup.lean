-- Prove2me | Theorems.Thm_MetricalTaskSystem_Randomized_randomizedRatio_ge_limsup
-- name    : MetricalTaskSystem.Randomized.randomizedRatio_ge_limsup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:19:17.118773+00:00
-- url     : https://prove2.me/theorems/9744036f-34d6-4004-8905-b14f023b1d0e
-- title:
--   Lemma 7.2 — Yao's principle for the randomized competitive ratio
-- statement:
--   Let $(S,d)$ be a task system and $s_0$ an initial state. Let the tasks come from a finite alphabet $\alpha$, letter $a$ standing for the nonnegative task $U_a$, and let $D$ be a probability measure on infinite letter sequences. Write $E$ for expectation under $D$, $\mathbf T^j$ for the first $j$ tasks, and
--   $$m_j=\inf_A E\big(c_A(\mathbf T^j)\big),$$
--   the infimum over all deterministic on-line algorithms $A$. Suppose that $E(c_0(\mathbf T^j))\to\infty$ as $j\to\infty$. Then for every $w$ such that some randomized on-line algorithm is expected $w$-competitive,
--   $$\limsup_{j\to\infty}\frac{m_j}{E\big(c_0(\mathbf T^j)\big)}\le w .$$
--   Equivalently, $\bar w(S,d)\ge\limsup_{j}m_j/E(c_0(\mathbf T^j))$ with the convention $\inf\emptyset=+\infty$.
--
--   The lemma turns a lower bound on the expected cost of every *deterministic* algorithm against one input distribution into a lower bound on the randomized competitive ratio.
--
--   **Formalization Note** The lemma is stated for distributions on sequences over a finite task alphabet, so that $E(c_A(\mathbf T^j))$ is a genuine expectation for every deterministic $A$; this covers the distribution used in the paper's application. The $\limsup$ is taken in the extended reals. The conclusion is stated for each achievable $w$ rather than for the real infimum $\bar w(S,d)$, whose value on an empty set would be $0$.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 759, Lemma 7.2

import Mathlib
import Definitions.Def_MetricalTaskSystem_Randomized_Model
import Definitions.Def_MetricalTaskSystem_Randomized_RandomizedAlgorithm
import Definitions.Def_MetricalTaskSystem_Randomized_TaskDistribution

namespace MetricalTaskSystem.Randomized

open MeasureTheory Filter

/-- **Lemma 7.2** (Borodin–Linial–Saks 1992, p. 759), for task sequences over a finite task
alphabet. Let `(S, d)` be a task system, `U : α → (S → ℝ)` a finite family of nonnegative tasks
and `D` a probability measure on infinite sequences of letters (so on infinite task sequences).
If `E(c₀(Tʲ)) → ∞`, then for every `w` such that some randomized on-line algorithm is expected
`w`-competitive, `limsup_j m_j / E(c₀(Tʲ)) ≤ w`, where `m_j` is the minimum over deterministic
on-line algorithms `A` of `E(c_A(Tʲ))`. This is `w̄(S, d) ≥ limsup_j m_j / E(c₀(Tʲ))` with
`inf ∅ = +∞`. -/
theorem randomizedRatio_ge_limsup {S α : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (d : S → S → ℝ) (hd : IsTaskSystem d)
    (U : α → S → ℝ) (hU : ∀ a s, 0 ≤ U a s)
    (D : Measure (ℕ → α)) [IsProbabilityMeasure D] (s₀ : S)
    (hE : Tendsto (fun j => expOfflineCost d s₀ U D j) atTop atTop)
    (R : RandomizedOnlineAlgorithm S) (w : ℝ) (hR : IsExpCompetitive d R w) :
    limsup (fun j : ℕ =>
        ((minDetExpCost d s₀ U D j / expOfflineCost d s₀ U D j : ℝ) : EReal)) atTop
      ≤ (w : EReal) := by sorry

end MetricalTaskSystem.Randomized
