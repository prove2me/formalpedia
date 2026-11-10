-- Prove2me | Theorems.Thm_MMSSevenNinths_Main_theorem_3_1
-- name    : MMSSevenNinths.Main.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:47:57.610907+00:00
-- url     : https://prove2.me/theorems/163b441f-973b-4097-baf4-d4e34729aa5a
-- title:
--   Theorem 3.1 — Algorithm 1 gives every agent with α_i ≤ MMS_i a bundle worth ≥ (7/9)α_i; failed agents have α_i > MMS_i
-- statement:
--   Let $I=(N,M,V)$ be an ordered instance with nonnegative additive valuations and $n\ge1$ agents, let $(\alpha_i)_{i\in N}$ be any real threshold vector, and consider any execution of Algorithm 1 on $(I,\alpha)$, i.e. any rule that chooses, whenever several active agents find the current bundle satisfactory, one of them. Then:
--
--   1. for every agent $i$ with $\alpha_i\le\mathrm{MMS}_i$, Algorithm 1 allocates to $i$ a bundle $B_i$ (she is not in the failed set) with $v_i(B_i)\ge\frac79\alpha_i$, whatever the other agents' thresholds and even if the call fails for other agents;
--   2. consequently, whenever Algorithm 1 returns $(\mathrm{FAILURE},F)$, every $i\in F$ satisfies $\alpha_i>\mathrm{MMS}_i$.
--
--   Differences from the source:
--   - encoding: Choose an arbitrary i ∈ A such that v_i(T) ≥ (7/9)α_i (and 'apply the reduction to an eligible agent') → a universally quantified recipient rule c : Chooser n with c.Valid (round index and eligible set ↦ an eligible agent); reason: every execution's sequence of choices is realized by such a rule indexed by the round, and every valid rule is an execution; same set of runs
--   - encoding: Algorithm 1 allocates to agent i a bundle B_i → i ∉ (alg1 V α c).failed and B_i = (alg1 V α c).bundles i; reason: the agents outside the final active set are exactly those that received a bundle; on success F = ∅
--   - encoding: ℓ ← max{j : ∃ i ∈ A, v_i(u_1 + u_j) ≥ (7/9)α_i} (similarly in the triple branch), indices running over the dummy-extended sequence → the last satisfactory candidate of the scan j = 2, …, |U|; reason: the satisfactory index k+1 lies in range; j = 1 cannot change a maximum at least k+1, and j > |U| leaves only {u_1}, unsatisfactory by failed R₀ in the pair branch or by the failed pair test in the triple branch
--   - encoding: agents N = {1,…,n} with n ≥ 1, goods e_1,…,e_m in the common order → agents Fin n (agent i+1 is i) with hypothesis 0 < n, goods Fin m (e_{g+1} is g); reason: zero-based finite indexing; n ≥ 1 is implicit in the MMS (an n-partition) and in v_i(M)/n; same instances
--   - encoding: u_1, u_2, … indexed residual goods padded with zero-valued dummies → resGood U r (one-based, none for a dummy) and resBundle dropping dummies; reason: dummies have value zero and are not goods of U; bundles are sets of real goods, as in §2.1
-- source:
--   Huang and Zhou (2026), A Strongly Polynomial-Time 7/9-Approximation Algorithm for Maximin Share Allocations, held STOC 2027 submission, SHA-256 428b298d196be354cea02bcd3b7278ffac7f04104c4bc290b02b6385aa0e405b, Theorem 3.1, printed pp. 6–7 (PDF 9–10)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MMSSevenNinths_Main_Instance
import Definitions.Def_MMSSevenNinths_Main_Algorithm1

namespace MMSSevenNinths.Main

open LittleCharity.MMS

/-- Huang and Zhou (2026), held STOC 2027 submission, Theorem 3.1, printed pp. 6–7 (PDF 9–10).
For every ordered instance with nonnegative additive valuations, every real threshold vector
`α`, and every execution of Algorithm 1 (every valid choice `c` of eligible recipients): each
agent `i` with `α_i ≤ MMS_i` is served (`i ∉ F`) with a bundle of value at least `(7/9) α_i`;
and whenever the call returns `(FAILURE, F)`, every `i ∈ F` has `α_i > MMS_i`. -/
theorem theorem_3_1 {n m : ℕ} (hn : 0 < n) (V : Fin n → Finset (Fin m) → ℝ)
    (hV : IsAdditive V) (hord : IsOrdered V) (α : Fin n → ℝ) (c : Chooser n)
    (hc : c.Valid) :
    (∀ i : Fin n, α i ≤ MMS V i →
      i ∉ (alg1 V α c).failed ∧ (7 / 9 : ℝ) * α i ≤ V i ((alg1 V α c).bundles i)) ∧
    ((alg1 V α c).success = false → ∀ i ∈ (alg1 V α c).failed, MMS V i < α i) := by sorry

end MMSSevenNinths.Main
