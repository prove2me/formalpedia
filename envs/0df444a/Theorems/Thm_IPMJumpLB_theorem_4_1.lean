-- Prove2me | Theorems.Thm_IPMJumpLB_theorem_4_1
-- name    : IPMJumpLB.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:34:35.909808+00:00
-- url     : https://prove2.me/theorems/e88f1c1d-9b74-46b4-b540-cfc5cd3fe8b0
-- title:
--   Theorem 4.1 — $L \ge k/(2\lceil 12bk^2/\eta\rceil) \ge \eta/(48bk) \ge \alpha k/48$ jumps, hence $\Omega(\sqrt{\hat m_k})$
-- statement:
--   Let $\alpha \in (0, 1)$, $b = \lceil 6/\alpha\rceil$, $k \ge 3$ and $\eta = \alpha \hat n_k$, where $\hat n_k = bk^2 + 1$ is the number of vertices of the unit-demand single-source shortest path instance of Section 4. Every $\eta$-path-following sequence of length $L$ on this instance (that is, every sequence of $L$ jumps between $\eta$-iterates) whose duality gaps satisfy $D^{(0)} \ge 6bk^3$ and $D^{(L)} \le k^3$ has
--   $$
--   L \ \ge\ \frac{k}{2\lceil 12bk^2/\eta\rceil} \ \ge\ \frac{\eta}{48bk} \ \ge\ \frac{\alpha k}{48} .
--   $$
--   In particular, for every fixed $\alpha \in (0, 1)$, every such sequence requires $\Omega(\sqrt{\hat m_k})$ jumps, where $\hat m_k = (2b-2)k^2 + k$ is the number of arcs.
--
--   Since every iterate is well centered ($\eta = \Omega(\hat n_k)$) and each jump may change either every slack or every flow by a factor of up to $2$, the theorem shows that reducing the duality gap by the constant factor $6b$ takes $\Omega(\sqrt{n})$ steps for every method captured by the model, including log-barrier, Lewis-weight and robust interior point methods.
--
--   **Formalization Note** The statement is a conjunction of the displayed chain (for all $\alpha$, $k$, $L$ and sequences) and the $\Omega$ clause, read as: for every $\alpha \in (0,1)$ there is $c > 0$ with $L \ge c\sqrt{\hat m_k}$ for every $k \ge 3$ and every such sequence, where $\hat m_k$ is the cardinality of the arc type. All quantities of the chain are compared in $\mathbb R$.
--
--   Differences from the source:
--   - reading: "requires Ω(√m̂_k) jumps for every fixed α" → for every α ∈ (0, 1) there is c > 0 such that L ≥ c·√m̂_k for every k ≥ 3 and every such sequence; reason: the explicit-constant reading uniform in k, which is what the printed chain gives (c = α/(48√(2b − 1)))
--   - encoding: b = ⌈6/α⌉ and η = α n̂_k as fixed values → universally quantified b, η with hypotheses b = ⌈6/α⌉₊ and η = α·n̂_k; reason: names for the paper's values, same instances
--   - encoding: Definition 2.3's range 1 ≤ η ≤ m for the parameter → not stated; reason: it is a range for the parameter, and η = α n̂_k lies in it for all α ∈ (0, 1), k ≥ 3 (checked)
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Theorem 4.1, p.11

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_slack
import Definitions.Def_IPMJumpLB_IsFlowFeasible
import Definitions.Def_IPMJumpLB_gap
import Definitions.Def_IPMJumpLB_IsEtaIterate
import Definitions.Def_IPMJumpLB_VertexU
import Definitions.Def_IPMJumpLB_ArcU
import Definitions.Def_IPMJumpLB_nHat
import Definitions.Def_IPMJumpLB_unitSSSP
import Definitions.Def_IPMJumpLB_IsJump
import Definitions.Def_IPMJumpLB_IsPathFollowing

namespace IPMJumpLB

/-- Theorem 4.1 (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), p.11). Let `α ∈ (0, 1)`, `b = ⌈6/α⌉`, `k ≥ 3` and `η = α n̂_k`. Every
sequence of `L` jumps between η-iterates on the Section 4 instance, with `D⁽⁰⁾ ≥ 6bk³` and
`D⁽ᴸ⁾ ≤ k³`, satisfies `L ≥ k/(2⌈12bk²/η⌉) ≥ η/(48bk) ≥ αk/48`. In particular, for every fixed
`α ∈ (0, 1)`, every such sequence requires `Ω(√m̂_k)` jumps.

**Formalization Note** The second clause reads `Ω(√m̂_k)` "for every fixed `α`" as: for every
`α ∈ (0, 1)` there is a constant `c > 0` such that `L ≥ c √m̂_k` for every `k ≥ 3` and every such
sequence, where `m̂_k` is the number of arcs. `b` and `η` are bound by equations. -/
theorem theorem_4_1 :
    (∀ (α : ℝ), 0 < α → α < 1 → ∀ (k : ℕ), 3 ≤ k → ∀ (b : ℕ), b = ⌈6 / α⌉₊ →
      ∀ (η : ℝ), η = α * (nHat b k : ℝ) →
      ∀ (L : ℕ) (seq : ℕ → (VertexU b k → ℝ) × (ArcU b k → ℝ)),
        IsPathFollowing (unitSSSP b k) η L seq →
        6 * (b : ℝ) * (k : ℝ) ^ 3 ≤ gap (unitSSSP b k) (seq 0).1 (seq 0).2 →
        gap (unitSSSP b k) (seq L).1 (seq L).2 ≤ (k : ℝ) ^ 3 →
        (k : ℝ) / (2 * (⌈12 * (b : ℝ) * (k : ℝ) ^ 2 / η⌉₊ : ℝ)) ≤ (L : ℝ) ∧
        η / (48 * (b : ℝ) * k) ≤ (k : ℝ) / (2 * (⌈12 * (b : ℝ) * (k : ℝ) ^ 2 / η⌉₊ : ℝ)) ∧
        α * k / 48 ≤ η / (48 * (b : ℝ) * k)) ∧
    (∀ (α : ℝ), 0 < α → α < 1 → ∃ c : ℝ, 0 < c ∧
      ∀ (k : ℕ), 3 ≤ k → ∀ (b : ℕ), b = ⌈6 / α⌉₊ →
      ∀ (η : ℝ), η = α * (nHat b k : ℝ) →
      ∀ (L : ℕ) (seq : ℕ → (VertexU b k → ℝ) × (ArcU b k → ℝ)),
        IsPathFollowing (unitSSSP b k) η L seq →
        6 * (b : ℝ) * (k : ℝ) ^ 3 ≤ gap (unitSSSP b k) (seq 0).1 (seq 0).2 →
        gap (unitSSSP b k) (seq L).1 (seq L).2 ≤ (k : ℝ) ^ 3 →
        c * Real.sqrt (Fintype.card (ArcU b k) : ℝ) ≤ (L : ℝ)) := by sorry

end IPMJumpLB
