-- Prove2me | Theorems.Thm_HarksKlimm_Consistency_local_monotonicity
-- name    : HarksKlimm.Consistency.local_monotonicity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:47.836422+00:00
-- url     : https://prove2.me/theorems/e12e804b-a3c8-48a2-872b-fb7ff03b8eeb
-- title:
--   Lemma 3.1 — Local characterization of monotonicity
-- statement:
--   Let $c:[0,\infty)\to\mathbb R$ be continuous. Then $c$ is nondecreasing or nonincreasing if and only if both of the following hold:
--   $$\forall x>0,\ c(x)>c(0)\Longrightarrow \exists\varepsilon>0\ \forall y\in(x,x+\varepsilon),\ c(y)\ge c(x),$$
--   $$\forall x>0,\ c(x)<c(0)\Longrightarrow \exists\varepsilon>0\ \forall y\in(x,x+\varepsilon),\ c(y)\le c(x).$$
--   The equivalence characterizes global monotonicity using one-sided local comparisons to the value at zero.
--
--   **Formalization Note** The domain is the nonnegative real half-line, including zero; costs take arbitrary real values.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, Lemma 3.1, p. 422 (PDF p. 4)

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

theorem local_monotonicity (c : ℝ≥0 → ℝ) (hc : Continuous c) :
    IsMonotonic c ↔
      (∀ x : ℝ≥0, 0 < x → c 0 < c x →
        ∃ ε : ℝ≥0, 0 < ε ∧ ∀ y : ℝ≥0, x < y → y < x + ε → c x ≤ c y) ∧
      (∀ x : ℝ≥0, 0 < x → c x < c 0 →
        ∃ ε : ℝ≥0, 0 < ε ∧ ∀ y : ℝ≥0, x < y → y < x + ε → c y ≤ c x) := by sorry

end HarksKlimm.Consistency
