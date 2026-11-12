-- Prove2me | Theorems.Thm_GreedySuperstring_LowerBound_greedy_invariants
-- name    : GreedySuperstring.LowerBound.greedy_invariants
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:07.677264+00:00
-- url     : https://prove2.me/theorems/ef12188e-89c3-42c4-8e84-639764a24d42
-- title:
--   Lemma 2.1 — all three invariants of every greedy execution
-- statement:
--   Let $S$ be any finite substring-free set of nonempty words over an alphabet. Consider any finite prefix of any legal maximum-overlap greedy execution, with chronological selected overlap lengths $l_1,\ldots,l_m$ and final current blocks $F$. Distinct current words remain substring-free. Each current block has a nonempty constituent history $t_1,\ldots,t_k$ and its actual word equals the paper's adjacent-prefix expression $\langle t_1,\ldots,t_k\rangle$. For two distinct current blocks with histories $t_1,\ldots,t_k$ and $t'_1,\ldots,t'_\ell$,
--
--   $$\operatorname{ov}(\langle t_1,\ldots,t_k\rangle,\langle t'_1,\ldots,t'_\ell\rangle)=\operatorname{ov}(t_k,t'_1).$$
--
--   Moreover,
--
--   $$l_1\ge l_2\ge\cdots\ge l_m.$$
--
--   All tie choices and all prefixes, including a zero-step prefix and a complete execution, are covered. This relates actual current overlaps to original endpoints without assuming the identity in the run relation.
--
--   Differences from the source:
--   - generalization: words over a finite alphabet → finite words over any type of symbols with decidable equality; reason: only the finitely many letters in the words are used; every finite alphabet admits an equality decision, so every source instance specializes
--   - encoding: a set of current strings formed in recorded constituent orders and nonincreasing selected lengths → finite sets of blocks with actual words and histories, explicit nonempty histories and adjacent-prefix equality, and pairwise earlier-later length inequalities; reason: histories start as singleton inputs and concatenate at updates; substring-freeness is stated for distinct blocks and thereby also prevents duplicate current words; no invariant is a run hypothesis
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, Lemma 2.1 (credited there to [BJL+94]), with §2.1–§2.2 standing assumptions, printed p.7 = PDF p.7

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_GreedyModel

universe invariant_u

namespace GreedySuperstring.LowerBound

/-- Lemma 2.1, printed/PDF p.7. Runs may be any finite prefix, including
zero steps. Histories only record the original words in concatenation order. -/
theorem greedy_invariants {α : Type invariant_u} [DecidableEq α]
    (S : Finset (List α)) (hne : ∀ s ∈ S, s ≠ []) (hsf : SubstringFree S)
    (ls : List ℕ) (F : Finset (Block α)) (hrun : GreedyRun (initialBlocks S) ls F) :
    (∀ a ∈ F, ∀ b ∈ F, a ≠ b → ¬ a.word <:+: b.word) ∧
    (∀ a ∈ F, a.history ≠ [] ∧ a.word = chainMerge a.history) ∧
    (∀ a ∈ F, ∀ b ∈ F, a ≠ b → ∀ x y : List α,
      a.history.getLast? = some x → b.history.head? = some y →
      overlap a.word b.word = overlap x y) ∧
    ls.Pairwise (fun x y => y ≤ x) := by sorry

end GreedySuperstring.LowerBound
