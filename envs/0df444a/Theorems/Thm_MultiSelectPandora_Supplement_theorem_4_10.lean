-- Prove2me | Theorems.Thm_MultiSelectPandora_Supplement_theorem_4_10
-- name    : MultiSelectPandora.Supplement.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:34:20.148758+00:00
-- url     : https://prove2.me/theorems/e8cc45eb-ade6-40a0-836f-bdcac4f7ef23
-- title:
--   Theorem 4.10 — two-phase structure of an optimal policy with one closed claim
-- statement:
--   Consider Pandora's box with nonobligatory inspection and $k\ge1$ selections, in which at most one of the selected boxes may be claimed closed ($\hat k=1$). A state $(U,\alpha)$ records the set $U$ of boxes neither opened nor claimed closed and the vector $\alpha_1\ge\dots\ge\alpha_k$ of the $k$ best values secured so far; $P(M,0)$ is the original problem. For a state, let
--   $$\tau=\tau_1\big(U,\alpha[1:k-1]\big)$$
--   be the phase threshold of Definition 4.2: the largest $x\in[0,\alpha_{k-1}]$ at which some optimal policy of $P\big(U,(\alpha[1:k-1],x)\big)$ claims a box closed with positive probability, and $-\infty$ if there is none.
--
--   **Theorem 4.10.** There exists an optimal policy $\pi^*$ for $P(M,0)$ such that for every reachable state $(U,\alpha)$, with $\tau=\tau_1(U,\alpha[1:k-1])$:
--
--   1. if $\alpha_k\le\tau$, then $\pi^*$ takes the same action at $(U,\alpha)$ as at $\big(U,(\alpha[1:k-1],0)\big)$;
--   2. if $\alpha_k>\tau$, then from $(U,\alpha)$ on, $\pi^*$ follows the generalized Weitzman policy (open boxes in nonincreasing order of reservation value, stop once the largest reservation value among unopened boxes is at most $\alpha_k$) and never claims a box closed.
--
--   While the $k$-th best observed value is at most the threshold, the optimal policy acts as if it were $0$; once it exceeds the threshold, the policy switches to the obligatory-inspection policy for good. This is the two-phase structure of the single-selection case extended to every $k$ with one closed claim; Section 4.1 shows it fails with two closed claims.
--
--   **Formalization Note** Policies are stationary state policies; a closed claim is part of the stopping action, so the claimed box is always selected; $\tau$ is a supremum in the extended reals; reachable states are those reached with positive probability from $(M,0)$; following the Weitzman policy is stated against one rule satisfying the published `IsWeitzmanRule`, with any tie-breaking.
--
--   Differences from the source:
--   - reading: an optimal policy π* (a policy acts on observation histories, §2.1); π* takes the same action at (U, α) as at (U, (α[1 : k−1], 0)) → π is a stationary deterministic state policy StPolicy I k, defined on every state (U, α); reason: the first bullet compares actions at two states, the second of which need not be reached, so π* must be a function of the state; (U, α) is a sufficient statistic (§2.2) and the policy the paper constructs (A0 fixed per pair, Algorithm 1, p.24) is of this form; every state policy is a policy
--   - reading: a closed claim as a separate action before stopping leading to (U \ {i}, top_k(α ∪ {E[v_i]}), k̂ − 1) (§2.2) → a closed claim is part of the stopping action (StAct.claimStop i, value α_1 + ⋯ + α_{k−1} + E[v_i]), as in the selection model of §2.1; reason: the claimed box is always selected (App. B.2 and the proof of Observation 4.1, p.37: 'a box claimed closed is one of the selected boxes'); in the §2.2 representation a claim of a box with E[v_i] < α_k is a free no-op, which would make 'claims a box closed with positive probability' hold at every large α_k; optimal values are the same in both
--   - encoding: optimal policy for P(M, 0) → IsOptimal I π univ 0: admissible, and expected utility at least that of every admissible state policy; reason: exact optimality; state policies attain the optimum over history policies
--   - reading: every reachable state (U, α) (k̂ = 1 omitted from the notation, §4.2) → every state reached with positive probability from (M, 0) before the process stops (Reach I π univ 0 U α); the remaining budget is 1 at each; reason: §4.2 omits k̂ = 1 from the state; a closed claim ends the process, so every state at which π acts has budget 1
--   - encoding: τ = τ1(U, α[1 : k − 1]), the largest x or −∞ → tau I U α : EReal, the sSup of the defining set (⊥ = −∞); α_k ≤ τ and α_k > τ compared in EReal; reason: App. B.2 shows the set is closed and bounded, so the supremum is the largest value; the empty set gives −∞ as on the page
--   - encoding: from (U, α) on, π* follows the generalized Weitzman policy and never claims a box closed → one rule with IsWeitzmanRule I k rule (any tie-breaking); at (U, α) and every state reached from it, π V β = StAct.ofRule (rule V β) and π V β ≠ claimStop i; reason: the published IsWeitzmanRule is a box-selection rule; following it means opening the box it names or stopping on none; 'never claims' is stated explicitly
--   - encoding: k a constant, α_k the k-th best value, explicit finite-support laws with c_i ≥ 0, v_i ≥ 0 → 1 ≤ k, α_k = stFloor α, Inst with Inst.Valid; reason: Lean convention of the published mission; selecting k ≥ 1 boxes is the paper's setting
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; preprint basis, sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Theorem 4.10, p.22 (PDF p.23); informal version Theorem 1.2, p.2 (PDF p.3); proof pp.23–24 (PDF pp.24–25) and App. B.3

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_Valid
import Definitions.Def_MultiSelectPandora_stFloor
import Definitions.Def_MultiSelectPandora_IsWeitzmanRule
import Definitions.Def_MultiSelectPandora_Supplement_StAct
import Definitions.Def_MultiSelectPandora_Supplement_StPolicy
import Definitions.Def_MultiSelectPandora_Supplement_Reach
import Definitions.Def_MultiSelectPandora_Supplement_IsOptimal
import Definitions.Def_MultiSelectPandora_Supplement_setLast
import Definitions.Def_MultiSelectPandora_Supplement_tau

namespace MultiSelectPandora.Supplement

/-- **Theorem 4.10 (two-phase structure with one closed claim).** Beyhaghi–Han–Luqman, *Multi-Selection Pandora's Box
with Nonobligatory Inspection*, manuscript (STOC 2027 submission), Theorem 4.10, p.22 (PDF p.23), with `k̂ = 1`
(§4.2): "There exists an optimal policy π∗ for P(M, 0) such that for every reachable state (U, α), writing
τ = τ1(U, α[1 : k − 1]): if αk ≤ τ, then π∗ takes the same action at (U, α) as at (U, (α[1 : k − 1], 0)); if αk > τ,
then from (U, α) on, π∗ follows the generalized Weitzman policy and never claims a box closed."

For every valid instance and every `k ≥ 1` there are a state policy `π` and a generalized Weitzman rule `rule` (any
tie-breaking) such that `π` is optimal for `P(M, 0)` and, at every state `(U, α)` reached with positive probability
from `(M, 0)`, with `τ = tau I U α`:
1. if `α_k ≤ τ`, the action at `(U, α)` equals the action at `(U, setLast α 0)`;
2. if `α_k > τ`, at `(U, α)` and at every state reached from it, `π` opens the box `rule` names or stops when `rule`
   returns `none`, and never claims a box closed.

**Formalization Note.** Policies are stationary state policies (`StPolicy`), the closed claim is part of the stopping
action (`StAct`, as in §2.1), `τ` is an `EReal` supremum (`⊥ = −∞`), and `α_k = stFloor α`. -/
theorem theorem_4_10 (I : Inst) (hI : I.Valid) (k : ℕ) (hk : 1 ≤ k) :
    ∃ (π : StPolicy I k) (rule : Finset (Fin I.n) → (Fin k → ℝ) → Option (Fin I.n)),
      IsOptimal I π Finset.univ (0 : Fin k → ℝ) ∧ IsWeitzmanRule I k rule ∧
      ∀ U α, Reach I π Finset.univ (0 : Fin k → ℝ) U α →
        (((stFloor α : ℝ) : EReal) ≤ tau I U α → π U α = π U (setLast α 0)) ∧
        (tau I U α < ((stFloor α : ℝ) : EReal) →
          ∀ V β, Reach I π U α V β →
            π V β = StAct.ofRule (rule V β) ∧ ∀ i, π V β ≠ StAct.claimStop i) := by sorry

end MultiSelectPandora.Supplement
