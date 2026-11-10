-- Prove2me | Theorems.Thm_MMSSevenNinths_Main_lemma_8_4
-- name    : MMSSevenNinths.Main.lemma_8_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:49:12.844909+00:00
-- url     : https://prove2.me/theorems/578f9e4d-1e79-43f4-bb91-c048b29a8e2c
-- title:
--   Lemma 8.4 — within a group, each agent's post-tail maximum takes O(Km²) values
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $I$ be an ordered instance with nonnegative additive valuations and $1\le n\le m$, and run the threshold search (Algorithm 14) on it. Consider a group of consecutive failed calls that all first reach tail filling with the same active agents $A_0$ and remaining goods $U_0$, and let $K=|A_0|$. For each call of the group and each agent $i\in F$ of that call, consider the largest value of $\frac97v_i(T)$ over her unsatisfactory bundles $T$ tested from the first tail-filling step onward. Then for each agent $i$ this maximum takes at most $C\,K\,m^2$ distinct values across the calls of the group.
--
--   Differences from the source:
--   - encoding: a group: a maximal block of consecutive failed calls with the same active agents and remaining goods at the first tail-filling step → any interval s ≤ t < e of consecutive failed calls with firstTail = some (A₀, U₀); reason: every finite part of a group is such an interval and every such interval lies in one group, so the bound for all intervals is the bound for groups, without assuming that a group is finite
--   - encoding: O(Km²) → ∃ C : ℕ before n, m, V and the group, with bound C·|A₀|·m²; reason: big-O with an absolute constant
--   - reading: from the first tail-filling step onward → the tests logged from the start of the tail-filling loop of the call's first tail-filling round (beginning with T = {u_1,u_{k+1},u_{2k+1}}) through the end of the call; reason: the step begins with the initial bag T; the earlier branch and R₃ tests of that round precede it
--   - reading: §8.1: scan candidates in increasing order of j when selecting the largest satisfactory index; record every tested bundle for every active agent → the scan tests j = 2, …, |U| ({u_1,u_j}, resp. {u_1,u_j,u_max(j+1,2k+1)}); reductions are tested in the order R₀,R₁,R₂ (resp. R₂, R₃) up to the first applicable one; tail filling tests T = {u_1,u_{k+1},u_{2k+1}} and then each enlarged bag; each test is logged with the active set; reason: the source fixes increasing scan order but leaves the finite range implicit; choose the distinct-good candidates j = 2, …, |U| and log every such test. A satisfactory candidate j = k+1 is in range. At j = 1 the pair repeats u_1 and the triple is {u_1,u_{2k+1}}; neither can change the largest satisfactory index. Beyond |U| the candidates reduce to {u_1}, which is unsatisfactory by the failed R₀ test in the pair branch or the failed pair test in the triple branch. The log is that of this explicitly fixed implementation
--   - encoding: agents N = {1,…,n} with n ≥ 1, goods e_1,…,e_m in the common order → agents Fin n (agent i+1 is i) with hypothesis 0 < n, goods Fin m (e_{g+1} is g); reason: zero-based finite indexing; n ≥ 1 is implicit in the MMS (an n-partition) and in v_i(M)/n; same instances
-- source:
--   Huang and Zhou (2026), A Strongly Polynomial-Time 7/9-Approximation Algorithm for Maximin Share Allocations, held STOC 2027 submission, SHA-256 428b298d196be354cea02bcd3b7278ffac7f04104c4bc290b02b6385aa0e405b, Lemma 8.4, printed p. 25 (PDF 28)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MMSSevenNinths_Main_Instance
import Definitions.Def_MMSSevenNinths_Main_Algorithm1
import Definitions.Def_MMSSevenNinths_Main_ThresholdSearch

namespace MMSSevenNinths.Main

open LittleCharity.MMS

/-- Huang and Zhou (2026), held STOC 2027 submission, Lemma 8.4, printed p. 25 (PDF 28).
There is an absolute constant `C` such that, for every ordered instance with nonnegative
additive valuations and `1 ≤ n ≤ m`, every group of consecutive failed calls `s, …, e-1` of
Algorithm 14 that first reach tail filling with the same active agents `A₀` (`K = |A₀|`) and
remaining goods `U₀`, and every agent `i`, the maximum of `9 v_i(T)/7` over the bundles `T` that
`i` finds unsatisfactory from the first tail-filling step onward takes at most `C K m²` distinct
values over the calls of the group in which `i` fails. -/
theorem lemma_8_4 :
    ∃ C : ℕ, ∀ (n m : ℕ), 0 < n → n ≤ m → ∀ V : Fin n → Finset (Fin m) → ℝ,
      IsAdditive V → IsOrdered V →
      ∀ (s e : ℕ) (A₀ : Finset (Fin n)) (U₀ : Finset (Fin m)),
        (∀ t, s ≤ t → t < e →
          (searchCall V t).success = false ∧ (searchCall V t).firstTail = some (A₀, U₀)) →
        ∀ i : Fin n,
          (((Finset.Ico s e).filter (fun t => i ∈ (searchCall V t).failed)).image
              (fun t => tailMax V t i)).card ≤ C * A₀.card * m ^ 2 := by sorry

end MMSSevenNinths.Main
