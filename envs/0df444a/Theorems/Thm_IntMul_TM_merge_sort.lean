-- Prove2me | Theorems.Thm_IntMul_TM_merge_sort
-- name    : IntMul.TM.merge_sort
-- status  : Open
-- author  : @avi
-- created : 2026-10-09T02:09:24.388783+00:00
-- url     : https://prove2.me/theorems/97769b99-51e5-4bb5-8a49-d7dc210a12f3
-- title:
--   Merge sort of $m$ records in time $O(N\log m)$ on a multitape Turing machine
-- statement:
--   **Sorting records on tapes.** There are a single deterministic multitape Turing machine $M$ and a constant $c>0$ with the following property. Let $\ell,q\ge0$ and let $(k_1,p_1),\dots,(k_m,p_m)$ be records, each consisting of a key $k_i\in\{0,1\}^\ell$ and a payload $p_i\in\{0,1\}^q$. On input
--   $$k_1\#p_1\#k_2\#p_2\#\cdots\#k_m\#p_m$$
--   of length $N$, the machine halts within $c\,(N+1)(\lceil\log_2m\rceil+1)$ steps and outputs the same records in the same format, **stably sorted** by the numerical value of the key (records with equal keys keep their input order).
--
--   This is the label-and-sort primitive used by Harvey and van der Hoeven for data rearrangements (e.g. the Agarwal–Cooley isomorphism in Proposition 5.4).
--
--   **Formalization Note** The output is specified as the encoding of Mathlib's stable `List.mergeSort` by $\operatorname{val}(k)$; since all keys have the same length, equal values mean equal keys. The input word determines the record list (records are separated by single $\#$s, keys and payloads alternate), so the required output is well defined. Machine model: `IntMul_MultitapeModel` with arbitrary inputs from `IntMul_MultitapeWords`.
-- source:
--   D. E. Knuth, The Art of Computer Programming, Vol. 3: Sorting and Searching, 2nd ed., Addison-Wesley 1998, §5.4 (external sorting / merging on tapes); used as 'merge sort in time O(tp log t) [31]' in Harvey–van der Hoeven, Ann. of Math. 193 (2021), proof of Proposition 4.7(ii), p. 33, and Proposition 5.4, step (2), p. 41.

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_MultitapeWords

namespace IntMul.TM

theorem merge_sort :
    ∃ M : MultitapeTM, ∃ c : ℝ, 0 < c ∧
      ∀ (ℓ q : ℕ) (recs : List (List Bool × List Bool)),
        (∀ r ∈ recs, r.1.length = ℓ ∧ r.2.length = q) →
        let enc : List (List Bool × List Bool) → List (Option Bool) := fun rs =>
          joinSep (rs.flatMap fun r => [bits r.1, bits r.2])
        ∃ t : ℕ,
          (t : ℝ) ≤ c * (((enc recs).length + 1 : ℕ) : ℝ) * ((Nat.clog 2 recs.length + 1 : ℕ) : ℝ) ∧
          M.HaltsWithOutputW (enc recs) t
            (enc (recs.mergeSort fun a b => decide (val a.1 ≤ val b.1))) := by sorry

end IntMul.TM
