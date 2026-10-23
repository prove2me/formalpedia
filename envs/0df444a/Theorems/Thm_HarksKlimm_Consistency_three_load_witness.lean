-- Prove2me | Theorems.Thm_HarksKlimm_Consistency_three_load_witness
-- name    : HarksKlimm.Consistency.three_load_witness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:52.339434+00:00
-- url     : https://prove2.me/theorems/60d483ac-f2f0-4a41-bc31-9e0ebe593c77
-- title:
--   Lemma 3.2 — Three-load witness
-- statement:
--   Let $c:[0,\infty)\to\mathbb R$ be continuous and neither nondecreasing nor nonincreasing. There exist $0<x<y$ such that
--   $$c(y-x)<c(y)<c(x)\quad\text{or}\quad c(y-x)>c(y)>c(x).$$
--   These three loads express opposing cost comparisons for unequal positive demands.
--
--   **Formalization Note** Variables lie in the nonnegative reals. The inequalities $0<x<y$ ensure $y>0$ and make the truncated subtraction $y-x$ equal ordinary positive real subtraction.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, Lemma 3.2, p. 423 (PDF p. 5)

import Definitions.Def_HarksKlimm_Consistency_IsMonotonic
set_option autoImplicit false
open scoped NNReal

/- Imported Lean declaration context (code only; not new declarations):

import Mathlib
set_option autoImplicit false

namespace HarksKlimm.Consistency

def IsMonotonic (c : ℝ≥0 → ℝ) : Prop := Monotone c ∨ Antitone c

end HarksKlimm.Consistency
-/

namespace HarksKlimm.Consistency

theorem three_load_witness (c : ℝ≥0 → ℝ) (hc : Continuous c)
    (hn : ¬ IsMonotonic c) :
    ∃ x y : ℝ≥0, 0 < x ∧ x < y ∧
      ((c (y - x) < c y ∧ c y < c x) ∨
       (c x < c y ∧ c y < c (y - x))) := by sorry

end HarksKlimm.Consistency
