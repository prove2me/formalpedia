-- Prove2me | Theorems.Thm_IncrOpenAddr_NoTradeoff_theorem_1_1
-- name    : IncrOpenAddr.NoTradeoff.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:36:32.746261+00:00
-- url     : https://prove2.me/theorems/4984df2f-2253-46c9-856b-79767a2ea361
-- title:
--   Theorem 1.1 — incremental open addressing with reordering: O(1) worst-case expected insertions, positive and negative queries at every load factor up to 1, no metadata but a counter
-- statement:
--   **Theorem 1.1.** There are a constant $C$, a word-size constant $c_w\ge1$ and one scheme $S$ (a probe function and two word-RAM programs INSERT and QUERY, the same for every $n$ and $w$) such that for every table size $n\ge1$ and every word size $w\ge c_w(\lfloor\log_2 n\rfloor+1)$:
--
--   1. for every hash function $f$ and every list $x_1,\dots,x_m$ of distinct $w$-bit keys with $m\le n$, inserting them in order into the empty $n$-slot array, every insertion halts and the final array holds each $x_k$ in exactly one slot and nothing else;
--   2. for every such list ending in $x$ (that is, every insertion, including the $n$-th, which fills the last empty slot), the expected number of steps of the insertion of $x$ is at most $C$;
--   3. for every $f$ and key $y$, the query for $y$ is oblivious: on every array and counter, its $k$-th slot read is $\mathrm{probe}(n,w,f,y,k)$;
--   4. for every such list $x_1,\dots,x_m$ and every key $y$, present or absent, on every $f$ the query for $y$ halts and answers "present" iff $y\in\{x_1,\dots,x_m\}$, and
--   $$\mathbb E_f\big[\mathrm{insertTime}\big]\le C,\qquad \mathbb E_f\big[\mathrm{queryTime}(f,x_{1..m},y)\big]\le C,$$
--   the expectations taken over a uniformly random hash function $f:\mathrm{Word}_w\times\mathrm{Word}_w\to\mathrm{Word}_w$ only.
--
--   The only persistent state of the table is the slot array, each slot empty or holding one key, and the element counter, maintained by the model and read-only to the programs. This is the paper's headline result: open addressing has no time–space tradeoff in the incremental setting, even at load factor $1$.
--
--   **Formalization Note.** Time is the number of executed word-RAM instructions (each `hash`, `slotRead`, `slotWrite` and `count` is one step), with value $\infty$ for a run that never halts. The answer of a query is the bit "cell $0\neq0$" when it halts.
--
--   Differences from the source:
--   - reading: an incremental open-addressed hash table with reordering (§1 clauses 1–3, footnote 1) → ∃ scheme S: a probe function probe n w f y k and two programs INSERT, QUERY, uniform in n and w; operations start on wiped scratch memory; the array Fin n → Option (Word w) is the only persistent state; QUERY never writes and is oblivious (its k-th slot read is probe n w f y k on every array content and counter); reason: this is the paper's model of open addressing made explicit on a word RAM
--   - reading: stores no metadata besides a counter of the number of elements present → the counter is maintained by the model (it equals the number of insertions so far) and both INSERT and QUERY may read it with COUNT; no program can write it; reason: clause 1 allows the counter as metadata; the paper's query does not read it, and allowing it changes nothing the counter could not already tell
--   - reading: words of Θ(log n) bits (App. A) → ∃ c_w ≥ 1 such that the claim holds for every w ≥ c_w·(⌊log₂ n⌋+1); keys are w-bit words; reason: specializes to w = c_w·(⌊log₂ n⌋+1); w may not depend on the keys
--   - reading: random hash functions, hash evaluations in constant time → one hash function f : Word w → Word w → Word w, uniform over all such functions, accessed only through the HASH instruction (one step per call); priority comparisons are done on words; reason: the paper's fully random hashing on a word RAM
--   - reading: O(1) worst-case expected time for insertions, positive queries and negative queries, at every load factor up to and including 1 → one natural constant C bounding E_f[steps] of every insertion (for every duplicate-free key list of length ≤ n ending in it) and of every query (for every such list and every key y); reason: 'worst-case expected': the bound holds for each fixed operation, expectation over f only
--   - reading: insertions succeed and queries are correct (Lemma 2.2 'Deterministically', Lemma 4.4 'At every time') → halting, the final array content and the query's answer are asserted for every hash function f; reason: the paper's correctness holds on every outcome, only time is in expectation
--   - encoding: time of an operation → number of executed instructions until halting, in ℕ∞ (⊤ if the run never halts); expectation as the average over all f in ℝ≥0∞; reason: a finite expected time then forces halting for every f, as each f has positive probability
--   - encoding: the input and output of an operation → each operation starts with n, w and its key in scratch cells 0, 1, 2 (all other cells 0), and the query answers 'present' iff cell 0 is nonzero when it halts; reason: a fixed calling convention for the programs; it changes no instance
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 2 (PDF 3), Theorem 1.1; restated and proved p. 25 (PDF 26)

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Machine
import Definitions.Def_IncrOpenAddr_NoTradeoff_Scheme

open scoped ENNReal

namespace IncrOpenAddr.NoTradeoff

theorem theorem_1_1 :
    ∃ C : ℕ, ∃ cw : ℕ, 1 ≤ cw ∧ ∃ S : Scheme,
      ∀ n w : ℕ, 1 ≤ n → cw * (Nat.log 2 n + 1) ≤ w →
        -- (a) every insertion halts and the array holds exactly the inserted keys
        (∀ (f : HashFn w) (xs : List (Word w)), xs.Nodup → xs.length ≤ n →
          ∃ A, tableAfter S n w f xs = some A ∧ HoldsExactly A xs) ∧
        -- (b) the expected time of every insertion, the last one included, is at most C
        (∀ (ys : List (Word w)) (x : Word w), (ys ++ [x]).Nodup → (ys ++ [x]).length ≤ n →
          expectHash (fun f => insertTime S n w f ys x) ≤ C) ∧
        -- (c) queries follow the fixed probe sequence, are always correct, and take
        -- expected time at most C, for present and absent keys alike
        (∀ (f : HashFn w) (y : Word w), IsOblivious S n w f y) ∧
        (∀ (xs : List (Word w)) (y : Word w), xs.Nodup → xs.length ≤ n →
          (∀ f : HashFn w, queryAnswer S n w f xs y = some (decide (y ∈ xs))) ∧
          expectHash (fun f => queryTime S n w f xs y) ≤ C) := by sorry

end IncrOpenAddr.NoTradeoff
