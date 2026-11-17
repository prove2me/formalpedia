-- Prove2me | Theorems.Thm_IncrementalER_Supplement_theorem_2_1
-- name    : IncrementalER.Supplement.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:51:21.898112+00:00
-- url     : https://prove2.me/theorems/a6234ed4-6c2a-4ca9-ad7c-a2fe5cb3c697
-- title:
--   Theorem 2.1 — terminal-robust sets under oblivious terminal requests
-- statement:
--   Fix a quasipolynomial capacity-ratio regime and a failure exponent $c>1$. For every connected positive-capacity multigraph $G$ with $n$ vertices and $m$ edge occurrences, every real $k>1$, and every oblivious sequence $v_1,\ldots,v_q$ of $q=\widetilde O(m/k)$ requests, one uniform randomized exact-real-RAM program maintains $T^{(0)},\ldots,T^{(q)}$ online such that:
--
--   1. $T^{(0)}$ is a $k$-hitting set, $|T^{(t)}|=\widetilde O(m/k)$, and $T^{(0)}\cup\{v_1,\ldots,v_t\}\subseteq T^{(t)}$;
--   2. the expected sum of the leverage degrees of vertices added and removed, evaluated in the corresponding new and old terminal sets, is $\widetilde O(m/k)$;
--   3. $\sum_t|T^{(t)}\mathbin\triangle T^{(t-1)}|=\widetilde O(m/k)$.
--
--   The total charged work is $\widetilde O(m\operatorname{poly}(k))$, and the whole sequence is correct with probability at least $1-n^{-c}$.
--
--   Differences from the source:
--   - encoding: informal algorithm, O-tilde bounds, expectation, and high probability → one admissible PNormReg exact-real-RAM program with uniform constants/exponents, lower-integral expectation, and a single coin-tape failure event; reason: this fixes the machine and the p.10 asymptotic conventions without changing any source instance
--   - encoding: capacitated multigraph used by Laplacian quantities → an edge list for multiplicity and work, collapsed to summed conductances only for Laplacian, leverage, and hitting quantities; reason: parallel edges have exactly the same Laplacian and random-walk conductances after summation
--   - generalization: graph edges join distinct vertices → edge-list inputs may also contain loops, which are ignored by every conductance, Laplacian, resistance, leverage, Schur-complement, and hitting-set quantity; reason: deleting the loops gives a source instance with identical mathematical outputs and no larger input-size bounds
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 2.1, pp.7 and 14

import Mathlib
import Definitions.Def_IncrementalER_Supplement_theorem21Spec

set_option autoImplicit false

namespace IncrementalER.Supplement

/-- **Theorem 2.1** (Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein,
*Incremental All-Pairs Effective Resistance in Almost-Linear Time*, STOC 2027 submission,
manuscript sha256 a0415fd5…, pp.7,14).

For every fixed quasipolynomial capacity-ratio regime and high-probability exponent, one admissible
exact-real-RAM program maintains terminal sets for an oblivious online request sequence with all
three printed guarantees: size and containment, expected two-sided leverage-change mass, and
unweighted recourse, together with the printed total-work and simultaneous high-probability bounds.

**Formalization Note.** `theorem21Spec` spells out the online cell protocol, the `k`-hitting-set
congestion parameter, `Õ` factors, both directions of leverage mass, recourse, total work and the
single whole-sequence failure event. -/
theorem theorem_2_1 :
    ∀ A : ℝ, 0 < A → ∀ q : ℕ, ∀ c : ℝ, 1 < c →
      ∃ P : PNormReg.Program, ∃ C : ℝ, ∃ r p : ℕ,
        A ≤ C ∧ q ≤ r ∧ theorem21Spec P C r p c := by sorry

end IncrementalER.Supplement
