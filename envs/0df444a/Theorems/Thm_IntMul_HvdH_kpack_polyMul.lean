-- Prove2me | Theorems.Thm_IntMul_HvdH_kpack_polyMul
-- name    : IntMul.HvdH.kpack_polyMul
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T22:50:44.880255+00:00
-- url     : https://prove2.me/theorems/0e3b7eb7-e19b-430a-9400-f7862defdef1
-- title:
--   Kronecker substitution is multiplicative
-- statement:
--   For any integer $B$ and coefficient lists $a,b$, evaluating at $B$ commutes with the schoolbook product:
--   $$\mathrm{kpack}_B(a\cdot b)=\mathrm{kpack}_B(a)\,\mathrm{kpack}_B(b).$$
--   This is the identity behind step (2) of Lemma 2.5 of Harvey–van der Hoeven (see `IntMul_HvdH_KronMul`).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 2.5 (Kronecker substitution)

import Definitions.Def_IntMul_HvdH_KronMul

namespace IntMul.HvdH
theorem kpack_polyMul (B : ℤ) (a b : List ℤ) :
    kpack B (polyMul a b) = kpack B a * kpack B b := by sorry
end IntMul.HvdH
