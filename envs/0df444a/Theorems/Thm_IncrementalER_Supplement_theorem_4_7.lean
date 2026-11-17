-- Prove2me | Theorems.Thm_IncrementalER_Supplement_theorem_4_7
-- name    : IncrementalER.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:53:53.640256+00:00
-- url     : https://prove2.me/theorems/fc76b8e6-2b7d-4c4b-8bbc-5e7c84fa51b2
-- title:
--   Theorem 4.7 — single-batch terminal augmentation
-- statement:
--   Let $S_0$ be a $k$-hitting set and let $Q_1,\ldots,Q_s$ contain $S_0$, where $s=\widetilde O(\operatorname{poly}(k))$. Given the initialized one-sided leverage-degree oracle and any batch $B$, one uniform randomized exact-real-RAM program returns $D$ in $\widetilde O(|B|\operatorname{poly}(k))$ charged work with
--   $$
--   B\subseteq D,\qquad |D|\le2|B|,
--   $$
--   and, for every fixed vertex $v$,
--   $$
--   \mathbb E\!\left[\frac1s\sum_i f_{Q_i\cup D}(v)\right]
--   \le \frac1s\sum_i f_{Q_i}(v)+O(1).
--   $$
--   The expectation is only over the fresh randomness of this batch algorithm.
--
--   Differences from the source:
--   - encoding: access to the initialized leverage-degree data structure → a one-sided constant-accuracy estimator exposed through a halt-and-resume oracle protocol, with the full query cost added to machine work; reason: this makes oracle access explicit without adding a free instruction to PNormReg
--   - encoding: expectation over batch randomness → a lower integral over a fresh fair-coin tape, while the retained sets and estimator are fixed outside the integral; reason: exactly preserves the probability scope printed after Theorem 4.7
--   - generalization: graph edges join distinct vertices → edge-list inputs may also contain loops, ignored by all graph quantities; reason: removing loops preserves the source instance and only decreases the size parameter used in upper bounds
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 4.7, p.19

import Mathlib
import Definitions.Def_IncrementalER_Supplement_theorem47Spec

set_option autoImplicit false

namespace IncrementalER.Supplement

/-- **Theorem 4.7** (Goranci et al., STOC 2027 submission, manuscript sha256 a0415fd5…, p.19).
Given the common hitting set, retained sets and a one-sided initialized leverage estimator, a
uniform charged-oracle program augments any one batch with the printed factor-two size, time and
expected average-cost guarantee.  The expectation is only over this batch program. -/
theorem theorem_4_7 :
    ∀ A : ℝ, 0 < A → ∀ q : ℕ,
      ∃ P : PNormReg.Program, ∃ C : ℝ, ∃ r p : ℕ,
        A ≤ C ∧ q ≤ r ∧ theorem47Spec P C r p := by sorry

end IncrementalER.Supplement
