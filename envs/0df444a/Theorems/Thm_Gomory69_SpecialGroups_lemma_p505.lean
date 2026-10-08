-- Prove2me | Theorems.Thm_Gomory69_SpecialGroups_lemma_p505
-- name    : Gomory69.SpecialGroups.lemma_p505
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:58:40.913622+00:00
-- url     : https://prove2.me/theorems/6c35a1af-34e4-4284-bdc1-28606892676b
-- title:
--   LEMMA, p. 505 — residues modulo p = 2 or 3
-- statement:
--   Let $p = 2$ or $p = 3$, and let $t, s$ be integers with $p > t > 0$ and $p > s \ge 0$. Then there are integers $t', t''$ with $t \ge t' \ge 0$, $t \ge t'' \ge 0$ and
--   $$t' + s \equiv t'' \pmod p .$$
--
--   This finite arithmetic fact is the only place where the exponents 2 and 3 enter the proof of THEOREM 23; it fails for $p = 5$ ($t = 1$, $s = 2$).
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 505, LEMMA

import Mathlib

namespace Gomory69.SpecialGroups

/-- The LEMMA of p. 505 (Gomory 1969): for `p = 2` or `p = 3`, if `t, s` are integers with
`p > t > 0` and `p > s ≥ 0`, there are integers `t', t''` with `t ≥ t' ≥ 0`, `t ≥ t'' ≥ 0` and
`t' + s ≡ t'' (mod p)`. -/
theorem lemma_p505 (p : ℤ) (hp : p = 2 ∨ p = 3) (t s : ℤ)
    (ht₀ : 0 < t) (htp : t < p) (hs₀ : 0 ≤ s) (hsp : s < p) :
    ∃ t' t'' : ℤ, 0 ≤ t' ∧ t' ≤ t ∧ 0 ≤ t'' ∧ t'' ≤ t ∧ t' + s ≡ t'' [ZMOD p] := by sorry

end Gomory69.SpecialGroups
