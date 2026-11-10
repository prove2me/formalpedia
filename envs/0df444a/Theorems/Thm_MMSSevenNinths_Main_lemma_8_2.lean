-- Prove2me | Theorems.Thm_MMSSevenNinths_Main_lemma_8_2
-- name    : MMSSevenNinths.Main.lemma_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:48:06.457899+00:00
-- url     : https://prove2.me/theorems/2ba93e66-5ab8-4dbe-ba2f-fbbf258bcb89
-- title:
--   Lemma 8.2 — safe threshold updates: MMS_i ≤ b_i < α_i for every failed agent
-- statement:
--   Let $I$ be an ordered instance with nonnegative additive valuations and $n\ge1$ agents, and let $\alpha$ be a threshold vector. Run the deterministic implementation of Algorithm 1 of §8.1 at $\alpha$ (candidates scanned in increasing order, the smallest-index eligible recipient, every tested bundle compared by every active agent). If the call returns $(\mathrm{FAILURE},F)$, then for every $i\in F$
--   $$\mathrm{MMS}_i\le b_i<\alpha_i,\qquad b_i=\max\{\tfrac97v_i(T): T\text{ tested in this call},\ v_i(T)<\tfrac79\alpha_i\}.$$
--
--   Differences from the source:
--   - generalization: for every failed call of the threshold search (Algorithm 14, §8 standing assumption n ≤ m, thresholds reached from v_i(M)/n) → for every threshold vector α and every n ≥ 1, m (no n ≤ m hypothesis); reason: the proof (Appendix D.1) uses only Theorem 3.1, valid for every α; the calls of Algorithm 14 are the special case α = thresholdSeq V t with n ≤ m
--   - reading: §8.1: scan candidates in increasing order of j when selecting the largest satisfactory index; record every tested bundle for every active agent → the scan tests j = 2, …, |U| ({u_1,u_j}, resp. {u_1,u_j,u_max(j+1,2k+1)}); reductions are tested in the order R₀,R₁,R₂ (resp. R₂, R₃) up to the first applicable one; tail filling tests T = {u_1,u_{k+1},u_{2k+1}} and then each enlarged bag; each test is logged with the active set; reason: the source fixes increasing scan order but leaves the finite range implicit; choose the distinct-good candidates j = 2, …, |U| and log every such test. A satisfactory candidate j = k+1 is in range. At j = 1 the pair repeats u_1 and the triple is {u_1,u_{2k+1}}; neither can change the largest satisfactory index. Beyond |U| the candidates reduce to {u_1}, which is unsatisfactory by the failed R₀ test in the pair branch or the failed pair test in the triple branch. The log is that of this explicitly fixed implementation
--   - encoding: agents N = {1,…,n} with n ≥ 1, goods e_1,…,e_m in the common order → agents Fin n (agent i+1 is i) with hypothesis 0 < n, goods Fin m (e_{g+1} is g); reason: zero-based finite indexing; n ≥ 1 is implicit in the MMS (an n-partition) and in v_i(M)/n; same instances
--   - encoding: b_i = max{9v_i(T)/7 : T tested in this call, v_i(T) < 7α_i/9} → failureBound V α i: the maximum (List.max?) over the call log entries (A, T) with i ∈ A and T unsatisfactory to i, with fallback α i when there is none; reason: for i ∈ F the final failed bag is such an entry, so the fallback is never used in the statement
-- source:
--   Huang and Zhou (2026), A Strongly Polynomial-Time 7/9-Approximation Algorithm for Maximin Share Allocations, held STOC 2027 submission, SHA-256 428b298d196be354cea02bcd3b7278ffac7f04104c4bc290b02b6385aa0e405b, Lemma 8.2, printed p. 25 (PDF 28)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MMSSevenNinths_Main_Instance
import Definitions.Def_MMSSevenNinths_Main_Algorithm1

namespace MMSSevenNinths.Main

open LittleCharity.MMS

/-- Huang and Zhou (2026), held STOC 2027 submission, Lemma 8.2 (safe threshold updates),
printed p. 25 (PDF 28). For every ordered instance with nonnegative additive valuations and
every threshold vector `α`, if the deterministic instrumented call of Algorithm 1 (§8.1) at `α`
returns `(FAILURE, F)`, then every `i ∈ F` satisfies `MMS_i ≤ b_i < α_i`, where `b_i` is the
largest `9 v_i(T)/7` over the bundles `T` tested in that call with `v_i(T) < 7α_i/9`. -/
theorem lemma_8_2 {n m : ℕ} (hn : 0 < n) (V : Fin n → Finset (Fin m) → ℝ)
    (hV : IsAdditive V) (hord : IsOrdered V) (α : Fin n → ℝ)
    (hfail : (alg1Det V α).success = false) :
    ∀ i ∈ (alg1Det V α).failed, MMS V i ≤ failureBound V α i ∧ failureBound V α i < α i := by sorry

end MMSSevenNinths.Main
