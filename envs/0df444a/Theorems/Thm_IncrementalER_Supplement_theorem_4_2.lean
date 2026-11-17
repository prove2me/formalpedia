-- Prove2me | Theorems.Thm_IncrementalER_Supplement_theorem_4_2
-- name    : IncrementalER.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:52:57.940827+00:00
-- url     : https://prove2.me/theorems/2f798850-5199-4c9c-b800-f52039900e82
-- title:
--   Theorem 4.2 — retained terminal sets with constant average insertion cost
-- statement:
--   For every connected positive-capacity graph with quasipolynomial capacity ratio and every real $k>1$, one uniform randomized exact-real-RAM program computes $s=\widetilde O(k^4)$ sets $Q_1,\ldots,Q_s$ such that
--   $$
--   \frac1s\sum_{i=1}^s f_{Q_i}(v)\le O(1)
--   $$
--   for every vertex $v$. With high probability the sets all contain one common $k$-hitting set $S_0$, satisfy $|Q_i|\le2|S_0|=\widetilde O(m/k)$, and are produced in $\widetilde O(m\operatorname{poly}(k))$ charged work.
--
--   Differences from the source:
--   - encoding: compute a sequence with O-tilde size/time and high probability → one admissible PNormReg program whose output memory contains s, S0, and every Qi, with uniform constants/exponents and one failure event; reason: fixes the unnamed machine and the p.10 asymptotic conventions while retaining the complete sequence output
--   - generalization: graph edges join distinct vertices → edge-list inputs may also contain loops, ignored by all graph quantities; reason: removing loops preserves the source instance and only decreases the size parameter used in upper bounds
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 4.2, p.16

import Mathlib
import Definitions.Def_IncrementalER_Supplement_theorem42Spec

set_option autoImplicit false

namespace IncrementalER.Supplement

/-- **Theorem 4.2** (Goranci et al., STOC 2027 submission, manuscript sha256 a0415fd5…, p.16).
One uniform program produces the whole retained sequence, its common `k`-hitting set, the pointwise
average insertion-cost guarantee, every size bound, total work and the simultaneous
high-probability event. -/
theorem theorem_4_2 :
    ∀ A : ℝ, 0 < A → ∀ q : ℕ, ∀ c : ℝ, 1 < c →
      ∃ P : PNormReg.Program, ∃ C : ℝ, ∃ r p : ℕ,
        A ≤ C ∧ q ≤ r ∧ theorem42Spec P C r p c := by sorry

end IncrementalER.Supplement
