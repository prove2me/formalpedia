-- Prove2me | Theorems.Thm_ImpatientQPTAS_theorem_2_6
-- name    : ImpatientQPTAS.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:02:00.385502+00:00
-- url     : https://prove2.me/theorems/32b0c378-0130-4953-87ed-6ebe4cdd5549
-- title:
--   Theorem 2.6 — rounding up costs a factor $1-2\epsilon$
-- statement:
--   Let $\epsilon\in(0,\tfrac14)$. Let $B$ be a set of average customers, $S$ an adaptive service policy, and let $p'$ agree with $p^\uparrow$ on $B$. Then there is an adaptive service policy $S^\uparrow$ with
--   $$
--   R^{(p')}_B(S^\uparrow)\ge(1-2\epsilon)\,R^{(p)}_B(S).
--   $$
--
--   This is the main technical result of the paper: despite customers departing at a higher rate, the rounded-up process nearly matches the original one.
--
--   Differences from the source:
--   - generalization: the optimal policy S* from [n], with every customer average → any policy S from any start set B of average customers; reason: at S = S*, B = [n] this is the printed statement; the proof of first_move uses subsets
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, Theorem 2.6, p.11; §3, pp.14–25

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Classes
import Definitions.Def_ImpatientQPTAS_Rounding

namespace ImpatientQPTAS

/-- Segev, arXiv:2209.13878v1, Theorem 2.6, p.11: there is an adaptive service policy `S↑` with
`R^(p↑)(S↑) ≥ (1 − 2ε)·R^(p)(S*)`.

**Formalization Note.** `ε ∈ (0, 1/4)` as in §2.1, p.7; the assumption that `1/ε` is a whole number, which §3 makes
"without loss of generality" (p.15), is a device of the proof, not a hypothesis of the theorem. The
statement holds from any start set `B` of average customers, and against any policy `S` in place of
`S*`; `B = univ` with every customer average is the printed setting. `p'` is `p↑` on `B`; no other
value of `p'` is ever read. -/
theorem theorem_2_6 {n : ℕ} (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 4) (I : Instance n)
    (hI : I.Standing) (B : Finset (Fin n)) (hB : B ⊆ Caverage ε I) (p' : Fin n → ℝ)
    (hp' : ∀ i ∈ B, p' i = pUp ε (I.p i)) (S : Policy n) (hS : IsPolicy S) :
    ∃ Su : Policy n, IsPolicy Su ∧
      (1 - 2 * ε) * I.Rfrom S B ≤ (⟨I.r, p'⟩ : Instance n).Rfrom Su B := by sorry

end ImpatientQPTAS
