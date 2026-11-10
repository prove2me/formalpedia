-- Prove2me | Theorems.Thm_MMSSevenNinths_Main_lemma_8_3
-- name    : MMSSevenNinths.Main.lemma_8_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:49:13.943204+00:00
-- url     : https://prove2.me/theorems/e9d0feb8-470e-40f5-8c4b-7aeb0f913b8e
-- title:
--   Lemma 8.3 — the state at the first tail-filling step changes O(n³m²) times across failed calls
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $I$ be an ordered instance with nonnegative additive valuations and $1\le n\le m$, and run the threshold search (Algorithm 14) on it: call $t$ runs the deterministic Algorithm 1 on the whole instance with thresholds starting at $\alpha_i=v_i(M)/n$ and updated simultaneously after each failed call by $\alpha_i\leftarrow b_i$ for $i\in F$. For each failed call, consider the active agents and remaining goods when that call first reaches tail filling. Across every run of consecutive failed calls $0,1,\dots,T-1$, these sets change between consecutive calls at most $C\,n^3m^2$ times.
--
--   Differences from the source:
--   - encoding: across the entire sequence of failed calls → for every T such that calls 0, …, T−1 all fail, the number of t < T−1 with firstTail(t) ≠ firstTail(t+1); reason: the failed calls form an initial segment of the search; a bound uniform in T is the bound for the whole sequence, without assuming that the search terminates
--   - encoding: O(n³m²) → ∃ C : ℕ before n, m, V and T, with bound C·n³·m²; reason: big-O with an absolute constant; uniform in every instance and value
--   - reading: §8.1: scan candidates in increasing order of j when selecting the largest satisfactory index; record every tested bundle for every active agent → the scan tests j = 2, …, |U| ({u_1,u_j}, resp. {u_1,u_j,u_max(j+1,2k+1)}); reductions are tested in the order R₀,R₁,R₂ (resp. R₂, R₃) up to the first applicable one; tail filling tests T = {u_1,u_{k+1},u_{2k+1}} and then each enlarged bag; each test is logged with the active set; reason: the source fixes increasing scan order but leaves the finite range implicit; choose the distinct-good candidates j = 2, …, |U| and log every such test. A satisfactory candidate j = k+1 is in range. At j = 1 the pair repeats u_1 and the triple is {u_1,u_{2k+1}}; neither can change the largest satisfactory index. Beyond |U| the candidates reduce to {u_1}, which is unsatisfactory by the failed R₀ test in the pair branch or the failed pair test in the triple branch. The log is that of this explicitly fixed implementation
--   - encoding: agents N = {1,…,n} with n ≥ 1, goods e_1,…,e_m in the common order → agents Fin n (agent i+1 is i) with hypothesis 0 < n, goods Fin m (e_{g+1} is g); reason: zero-based finite indexing; n ≥ 1 is implicit in the MMS (an n-partition) and in v_i(M)/n; same instances
-- source:
--   Huang and Zhou (2026), A Strongly Polynomial-Time 7/9-Approximation Algorithm for Maximin Share Allocations, held STOC 2027 submission, SHA-256 428b298d196be354cea02bcd3b7278ffac7f04104c4bc290b02b6385aa0e405b, Lemma 8.3, printed p. 25 (PDF 28)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MMSSevenNinths_Main_Instance
import Definitions.Def_MMSSevenNinths_Main_Algorithm1
import Definitions.Def_MMSSevenNinths_Main_ThresholdSearch

namespace MMSSevenNinths.Main

open LittleCharity.MMS

/-- Huang and Zhou (2026), held STOC 2027 submission, Lemma 8.3, printed p. 25 (PDF 28).
There is an absolute constant `C` such that, for every ordered instance with nonnegative
additive valuations and `1 ≤ n ≤ m`, and every finite run of consecutive failed calls
`0, …, T-1` of Algorithm 14, the residual state (active agents, remaining goods) at the first
tail-filling step changes between consecutive calls at most `C n³ m²` times. -/
theorem lemma_8_3 :
    ∃ C : ℕ, ∀ (n m : ℕ), 0 < n → n ≤ m → ∀ V : Fin n → Finset (Fin m) → ℝ,
      IsAdditive V → IsOrdered V →
      ∀ T : ℕ, (∀ t < T, (searchCall V t).success = false) →
        ((List.range (T - 1)).filter
            (fun t => decide ((searchCall V t).firstTail ≠ (searchCall V (t + 1)).firstTail))).length
          ≤ C * n ^ 3 * m ^ 2 := by sorry

end MMSSevenNinths.Main
