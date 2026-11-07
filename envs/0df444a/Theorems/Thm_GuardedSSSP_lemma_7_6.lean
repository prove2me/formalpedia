-- Prove2me | Theorems.Thm_GuardedSSSP_lemma_7_6
-- name    : GuardedSSSP.lemma_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:10.746926+00:00
-- url     : https://prove2.me/theorems/b37697ae-d153-441a-8886-2b5da18e57d7
-- title:
--   Lemma 7.6 — the integer evaluator satisfies $f_d(x)\le\widehat f_d(x)\le8f_d(x)$ with $O(d+1)$ word operations
-- statement:
--   For every generation $d$ and every integer scale $x\ge0$,
--
--   $$f_d(x)\le\widehat f_d(x)\le8f_d(x),$$
--
--   where $\widehat f_d(x)$ is defined by (30). The routine that evaluates (30) with word operations returns $\widehat f_d(x)$, and for every constant $c_0$ there is $C$ such that whenever $d\le c_0(\log^*_2(x+2)+1)$ it uses at most $C(d+1)$ word operations and every integer it forms is at most $(x+2)^C$, i.e. has $O(\log(x+2))$ bits.
--
--   The evaluator lets the solver compute the factor $f_d$ to within a constant factor with integer metadata only.
--
--   Differences from the source:
--   - encoding: word operations and O(log(x+2))-bit words of the routine (30) → the operation count and largest intermediate of the instrumented function fhatRun, which follows (30) step by step; reason: the lemma's own cost model, "assuming bit length as a metadata primitive"
--   - encoding: At d = O(log∗₂(x+2)) → for every c₀, ∃ C, whenever d ≤ c₀(log∗₂(x+2) + 1); reason: the meaning of O(·), with the +1 covering small x
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Lemma 7.6 with display (30), p.16 (PDF p.17)

import Mathlib
import Definitions.Def_GuardedSSSP_LogHierarchy
import Definitions.Def_GuardedSSSP_fhat

namespace GuardedSSSP

/-- **Lemma 7.6** (Integer evaluator) with display (30), p.16 (PDF p.17).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…): "The routine (30) satisfies f_d(x) ≤ f̂_d(x) ≤ 8f_d(x). At
d = O(log∗₂(x+2)) it uses O(d + 1) word operations, assuming bit length as a metadata primitive, and
O(log(x + 2))-bit words with fixed headroom."

Clauses, for integer scales `x ≥ 0`:
1. `f_d(x) ≤ f̂_d(x) ≤ 8 f_d(x)` for every `d`;
2. the instrumented routine `fhatRun` returns `f̂_d(x)`;
3. for every `c₀` there is `C` such that whenever `d ≤ c₀(log*₂(x + 2) + 1)`, the routine uses at most
   `C(d + 1)` word operations and every integer it forms is at most `(x + 2)^C`, i.e. has
   `O(log(x + 2))` bits.

**Formalization Note.** The cost clause is stated on the instrumented pure function `fhatRun`, which
follows (30) step by step and charges one unit per addition, subtraction, shift, division and bit length;
this is the lemma's own cost model ("assuming bit length as a metadata primitive"). "d = O(log*₂(x + 2))"
is `d ≤ c₀(log*₂(x+2) + 1)` for an arbitrary `c₀`, with `C` chosen after `c₀`. -/
theorem lemma_7_6 :
    (∀ d x : ℕ, f d x ≤ (fhat d x : ℝ) ∧ (fhat d x : ℝ) ≤ 8 * f d x) ∧
    (∀ d x : ℕ, (fhatRun d x).1 = fhat d x) ∧
    (∀ c₀ : ℝ, ∃ C : ℕ, ∀ d x : ℕ, (d : ℝ) ≤ c₀ * ((logStar ((x : ℝ) + 2) : ℝ) + 1) →
      (fhatRun d x).2.1 ≤ C * (d + 1) ∧ (fhatRun d x).2.2 ≤ (x + 2) ^ C) := by sorry

end GuardedSSSP
