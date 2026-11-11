-- Prove2me | Theorems.Thm_MatchIndiff_PublicSM_lemma_6_1
-- name    : MatchIndiff.PublicSM.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:26:23.651474+00:00
-- url     : https://prove2.me/theorems/ee3ed097-c875-4396-95d9-568c4f3fa557
-- title:
--   Lemma 6.1 — a non-revisiting trace with overlapping steps is the whole strict stable set
-- statement:
--   Let $M_0,\dots,M_L$ be a trace of perfect matchings of $n$ students and $n$ schools in which each step replaces the pairs on one alternating cycle. Suppose no student visits a school twice after leaving it, and every two consecutive steps share a student. Give each student exactly its visited schools, ordered from earlier to later visits (a strict row), and let $Q$ be any strict complete school priority profile that ranks each school's visited holders in reverse chronological order and places all other students below them. Then for this strict market the stable set is exactly
--   $$\{\mu:\ \mu\ \text{stable}\}=\{M_0,\dots,M_L\}.$$
--   It is the strict-market engine of the lower bound: Algorithm 1's trace satisfies the hypotheses (Lemma 6.2), and tying boundaries of the chronological lists deletes trace positions (Lemma 6.3).
--
--   **Formalization Note.** The trace is `M : ℕ → Fin n → Fin n` on positions $0..L$; a step $t\to t+1$ is one alternating cycle when $M_{t+1}=M_t\circ\sigma$ for a cyclic permutation $\sigma$ of the students.
--
--   Differences from the source:
--   - reading: the entire strict stable set → for each α ∈ {weak, strong, super}, the α-stable set of the strict market; reason: on strict rows and strict priorities the three blocking notions coincide (p. 7, Lemma 2.3's proof), so this is the same set
--   - reading: trace of perfect matchings, a step replaces the pairs on one alternating cycle → M t bijective for t ≤ L, and M (t+1) = M t ∘ σ with σ a cyclic permutation (Equiv.Perm.IsCycle); reason: the paper's definition of a trace and a step (p. 10)
--   - reading: place all other students below them in any fixed strict order → every Q with IsRevChronPriority: strict, complete, gap-free rows, visited holders in reverse chronological order, all visited holders above all others; reason: the lemma quantifies over the arbitrary fixed order
--   - encoding: matchings M_t, rows ordered by visits → M : ℕ → Fin n → Fin n, chronRow via markedRank with no marks; the stable set is described by ∃ t ≤ L, ∀ s, μ s = some (M t s); reason: Lean convention
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 11, Lemma 6.1

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model
import Definitions.Def_MatchIndiff_PublicSM_Trace

namespace MatchIndiff.PublicSM

/-- Lemma 6.1 (p. 11): let `M_0, …, M_L` be a trace of perfect matchings of `n` students and `n`
schools, each step replacing the pairs on one alternating cycle. If no student revisits a school
after leaving it and every two consecutive steps share a student, then with the chronological
student lists and any strict complete school priorities ranking visited holders in reverse
chronological order above all other students, the stable set is exactly `{M_0, …, M_L}`. -/
theorem lemma_6_1 {n L : ℕ} (M : ℕ → Fin n → Fin n)
    (hperf : ∀ t ≤ L, Function.Bijective (M t))
    (hstep : ∀ t < L, ∃ σ : Equiv.Perm (Fin n), σ.IsCycle ∧ ∀ s, M (t + 1) s = M t (σ s))
    (hnr : NoRevisit M L) (hsh : ConsecShare M L)
    (Q : Fin n → Fin n → ℕ) (hQ : IsRevChronPriority M L Q) (α : StabKind) (μ : Matching n n) :
    IsStable α (chronRow M L) Q μ ↔ ∃ t ≤ L, ∀ s, μ.toFun s = some (M t s) := by sorry

end MatchIndiff.PublicSM
