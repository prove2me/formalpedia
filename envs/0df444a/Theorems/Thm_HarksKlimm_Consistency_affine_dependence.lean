-- Prove2me | Theorems.Thm_HarksKlimm_Consistency_affine_dependence
-- name    : HarksKlimm.Consistency.affine_dependence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:48.721055+00:00
-- url     : https://prove2.me/theorems/05da8ff2-7509-4952-9b4f-b118723aef01
-- title:
--   Lemma 4.1 — Affine dependence of two nonconstant functions
-- statement:
--   Let $c_1,c_2:[0,\infty)\to\mathbb R$ be continuous, monotonic and nonconstant. Then
--   $$\bigl(\forall a_1,a_2\in\mathbb Z,\ a_1c_1+a_2c_2\text{ is monotonic}\bigr)
--   \Longleftrightarrow
--   \bigl(\exists a,b\in\mathbb R\ \forall x\ge0,\ c_2(x)=ac_1(x)+b\bigr).$$
--   This identifies the compatibility condition imposed by monotonicity of every integer combination.
--
--   **Formalization Note** Monotonicity allows either weak direction. Each nonconstancy hypothesis gives two points with different values on the entire closed half-line. The faithful statement retains both continuity hypotheses.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, Lemma 4.1, p. 425 (PDF p. 7)

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

theorem affine_dependence (c₁ c₂ : ℝ≥0 → ℝ)
    (hc₁ : Continuous c₁) (hc₂ : Continuous c₂)
    (hm₁ : IsMonotonic c₁) (hm₂ : IsMonotonic c₂)
    (hn₁ : ∃ x y, c₁ x ≠ c₁ y) (hn₂ : ∃ x y, c₂ x ≠ c₂ y) :
    (∀ a₁ a₂ : ℤ, IsMonotonic (fun x => (a₁ : ℝ) * c₁ x + (a₂ : ℝ) * c₂ x)) ↔
      ∃ a b : ℝ, ∀ x : ℝ≥0, c₂ x = a * c₁ x + b := by sorry

end HarksKlimm.Consistency
