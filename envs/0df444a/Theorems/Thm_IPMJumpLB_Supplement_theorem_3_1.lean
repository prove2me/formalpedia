-- Prove2me | Theorems.Thm_IPMJumpLB_Supplement_theorem_3_1
-- name    : IPMJumpLB.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:50:08.69829+00:00
-- url     : https://prove2.me/theorems/93e67449-e6da-4ac8-8799-859e49178a7d
-- title:
--   Theorem 3.1 — on the Section 3.1 instance, $L \ge k/(2\lceil 16k^2/\eta\rceil) \ge \eta/(64k)$ jumps, hence $\Omega(\sqrt{m_k})$ when $\eta = \Omega(n_k)$
-- statement:
--   Let $k \ge 3$ be an integer and consider the hard min-cost flow instance of Section 3.1 on $n_k = k^2 + k + 1$ vertices and $m_k = 2k^2 + 2k$ arcs: a bidirected main path $v_0, \dots, v_k$ with unit arc costs, and $k^2$ shortcut paths $v_0 \to a_j \to v_k$ whose arcs cost $k$; the demands are $d_{v_0} = 2k$, $d_{v_i} = -1$ for $1 \le i < k$, $d_{v_k} = -(k+1)$ and $d_{a_j} = 0$. For a primal-dual point $(x, f)$ with slacks $s = c - Bx$, write $D = \langle s, f\rangle$ for the duality gap. An **$\eta$-iterate** is a strictly feasible point ($B^\top f = d$, $f > 0$, $s > 0$) with $\max_e s_e f_e \le D/\eta$; a **jump** between $\eta$-iterates multiplies every slack, or every flow, by a factor in $[1/2, 2]$.
--
--   **Theorem.**
--
--   1. Let $8k \le \eta \le m_k$. Every sequence of $L$ jumps between $\eta$-iterates $(x^{(0)}, f^{(0)}), \dots, (x^{(L)}, f^{(L)})$ with $D^{(0)} \ge 8k^2$ and $D^{(L)} \le k^2$ satisfies
--   $$
--   L \;\ge\; \frac{k}{2\lceil 16k^2/\eta\rceil} \;\ge\; \frac{\eta}{64k}.
--   $$
--   2. In particular, if $\eta = \Omega(n_k)$, every such sequence requires $\Omega(\sqrt{m_k})$ jumps: for every $c > 0$ there is $c' > 0$ such that for all $k \ge 3$ and all $\eta$ with $c\,n_k \le \eta$ and $8k \le \eta \le m_k$, every such sequence has $L \ge c'\sqrt{m_k}$.
--
--   This is the paper's first lower bound in its path-following model: reducing the duality gap by a constant factor on this min-cost flow instance takes $\Omega(\sqrt{m})$ jumps when $\eta$ is linear in the number of vertices. Theorem 4.1, the mission's goal, adapts the instance to unit-demand single-source shortest paths.
--
--   **Formalization Note** The $\eta$-iterates, jumps and path-following sequences are the published definitions of the base mission (`IsEtaIterate`, `IsJump`, `IsPathFollowing`); the sequence is a map from $\mathbb N$ constrained on $0, \dots, L$. $n_k$ and $m_k$ appear as the polynomials $k^2 + k + 1$ and $2k^2 + 2k$, which are the cardinalities of the vertex and arc types. The ceiling is the natural-number ceiling of the positive real $16k^2/\eta$.
--
--   Differences from the source:
--
--   - encoding: an η-iterate is a triple (x, s, f) with D_max(s, f) ≤ D(s, f)/η → the pair (x, f) with s = c − Bx computed, and ∀ e, η·s_e f_e ≤ ⟨s, f⟩; reason: the base mission's published convention; the two forms are equivalent on every instance
--   - encoding: jump conditions ½ s_e ≤ s'_e ≤ 2 s_e or ½ f_e ≤ f'_e ≤ 2 f_e → ratios 1/2 ≤ s'_e/s_e ≤ 2 or 1/2 ≤ f'_e/f_e ≤ 2 of positive reals; reason: the base mission's published convention; equivalent since both endpoints are η-iterates
--   - encoding: n_k and m_k (Eq. (7)) → the polynomials k² + k + 1 and 2k² + 2k; reason: they are the paper's values and equal the cardinalities of the vertex and arc types
--   - encoding: the sequence ℓ = 0, …, L → a map ℕ → (V_k → ℝ) × (E_k → ℝ) constrained only on 0, …, L; reason: the base mission's published convention; same sequences
--   - reading: if η = Ω(n_k), every such sequence requires Ω(√m_k) jumps → ∀ c > 0, ∃ c' > 0, ∀ k ≥ 3, ∀ η with c·n_k ≤ η and 8k ≤ η ≤ m_k, every such sequence has c'·√m_k ≤ L; reason: the asymptotic clause is informal; this is the standard reading with c' uniform in k, η and the sequence, the shape of the published goal's Ω clause
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Theorem 3.1, p.7 (instance §3.1 and Eq. (7), p.6)

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_slack
import Definitions.Def_IPMJumpLB_IsFlowFeasible
import Definitions.Def_IPMJumpLB_gap
import Definitions.Def_IPMJumpLB_IsEtaIterate
import Definitions.Def_IPMJumpLB_IsJump
import Definitions.Def_IPMJumpLB_IsPathFollowing
import Definitions.Def_IPMJumpLB_Supplement_VertexS
import Definitions.Def_IPMJumpLB_Supplement_ArcS
import Definitions.Def_IPMJumpLB_Supplement_minCostFlowInstance

namespace IPMJumpLB

namespace Supplement

/-- Theorem 3.1 (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), p.7). On the instance of Section 3.1, let
`8k ≤ η ≤ m_k`. Every sequence of `L` jumps between η-iterates with `D⁽⁰⁾ ≥ 8k²` and
`D⁽ᴸ⁾ ≤ k²` satisfies `L ≥ k/(2⌈16k²/η⌉) ≥ η/(64k)`. In particular, if `η = Ω(n_k)`, every such
sequence requires `Ω(√m_k)` jumps.

**Formalization Note** `n_k = k² + k + 1` and `m_k = 2k² + 2k` (Eq. (7), p.6) are written as
these polynomials; they are the cardinalities of `VertexS k` and `ArcS k`. `k` is an integer
`k ≥ 3` (§3.1). The ceiling is `Nat.ceil` of the real `16k²/η`. The second clause reads
"if `η = Ω(n_k)`, … `Ω(√m_k)` jumps" as: for every `c > 0` there is `c' > 0` such that, for every
`k ≥ 3` and every `η` with `c·n_k ≤ η` and `8k ≤ η ≤ m_k`, every such sequence has `L ≥ c'√m_k`;
`c'` depends only on `c`. -/
theorem theorem_3_1 :
    (∀ (k : ℕ), 3 ≤ k → ∀ (η : ℝ), 8 * (k : ℝ) ≤ η → η ≤ 2 * (k : ℝ) ^ 2 + 2 * (k : ℝ) →
      ∀ (L : ℕ) (seq : ℕ → (VertexS k → ℝ) × (ArcS k → ℝ)),
        IsPathFollowing (minCostFlowInstance k) η L seq →
        8 * (k : ℝ) ^ 2 ≤ gap (minCostFlowInstance k) (seq 0).1 (seq 0).2 →
        gap (minCostFlowInstance k) (seq L).1 (seq L).2 ≤ (k : ℝ) ^ 2 →
        (k : ℝ) / (2 * (⌈16 * (k : ℝ) ^ 2 / η⌉₊ : ℝ)) ≤ (L : ℝ) ∧
        η / (64 * (k : ℝ)) ≤ (k : ℝ) / (2 * (⌈16 * (k : ℝ) ^ 2 / η⌉₊ : ℝ))) ∧
    (∀ (c : ℝ), 0 < c → ∃ c' : ℝ, 0 < c' ∧
      ∀ (k : ℕ), 3 ≤ k → ∀ (η : ℝ), c * ((k : ℝ) ^ 2 + (k : ℝ) + 1) ≤ η →
      8 * (k : ℝ) ≤ η → η ≤ 2 * (k : ℝ) ^ 2 + 2 * (k : ℝ) →
      ∀ (L : ℕ) (seq : ℕ → (VertexS k → ℝ) × (ArcS k → ℝ)),
        IsPathFollowing (minCostFlowInstance k) η L seq →
        8 * (k : ℝ) ^ 2 ≤ gap (minCostFlowInstance k) (seq 0).1 (seq 0).2 →
        gap (minCostFlowInstance k) (seq L).1 (seq L).2 ≤ (k : ℝ) ^ 2 →
        c' * Real.sqrt (2 * (k : ℝ) ^ 2 + 2 * (k : ℝ)) ≤ (L : ℝ)) := by sorry

end Supplement

end IPMJumpLB
