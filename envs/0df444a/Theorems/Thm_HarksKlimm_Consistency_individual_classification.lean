-- Prove2me | Theorems.Thm_HarksKlimm_Consistency_individual_classification
-- name    : HarksKlimm.Consistency.individual_classification
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:51.852075+00:00
-- url     : https://prove2.me/theorems/de304b47-ae17-475b-9ab1-d0a81fa7e064
-- title:
--   Lemma 5.1 — Affine or exponential individual functions
-- statement:
--   Let $C$ be a set of continuous functions on $[0,\infty)$. Then
--   $$\mathcal L_{\mathbb Z}^3(C)\text{ contains only monotonic functions}
--   \Longleftrightarrow
--   \forall c\in C,\quad \bigl(\exists a,b,\varphi\in\mathbb R\ \forall x\ge0,\ c(x)=ae^{\varphi x}+b\bigr)
--   \ \text{or}\ \bigl(\exists a,b\in\mathbb R\ \forall x\ge0,\ c(x)=ax+b\bigr).$$
--   This classifies each individual function from monotonicity of integer combinations with its translates.
--
--   **Formalization Note** All identities include zero. Here the exponential rate may depend on $c$, unlike the common rate in Theorem 5.1. Constants and an empty class are allowed.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, Lemma 5.1, p. 426 (PDF p. 8)

import Definitions.Def_HarksKlimm_Consistency_ShiftHull
import Definitions.Def_HarksKlimm_Consistency_IsMonotonic
import Definitions.Def_HarksKlimm_Consistency_IsAffine
import Definitions.Def_HarksKlimm_Consistency_IsExponential
set_option autoImplicit false
open scoped NNReal

/- Imported Lean declaration context (code only; not new declarations):

import Mathlib
set_option autoImplicit false

namespace HarksKlimm.Consistency

def ShiftHull (C : Set (ℝ≥0 → ℝ)) : Set (ℝ≥0 → ℝ) :=
  {h | ∃ (a₁ a₂ : ℤ) (c : ℝ≥0 → ℝ) (δ : ℝ≥0),
    c ∈ C ∧ 0 < δ ∧ ∀ x, h x = (a₁ : ℝ) * c x + (a₂ : ℝ) * c (x + δ)}

end HarksKlimm.Consistency

import Mathlib
set_option autoImplicit false

namespace HarksKlimm.Consistency

def IsMonotonic (c : ℝ≥0 → ℝ) : Prop := Monotone c ∨ Antitone c

end HarksKlimm.Consistency

import Mathlib
set_option autoImplicit false

namespace HarksKlimm.Consistency

def IsAffine (c : ℝ≥0 → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ x : ℝ≥0, c x = a * (x : ℝ) + b

end HarksKlimm.Consistency

import Mathlib
set_option autoImplicit false

namespace HarksKlimm.Consistency

def IsExponential (φ : ℝ) (c : ℝ≥0 → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ x : ℝ≥0, c x = a * Real.exp (φ * (x : ℝ)) + b

end HarksKlimm.Consistency
-/

namespace HarksKlimm.Consistency

theorem individual_classification (C : Set (ℝ≥0 → ℝ))
    (hC : ∀ c ∈ C, Continuous c) :
    (∀ h ∈ ShiftHull C, IsMonotonic h) ↔
      ∀ c ∈ C, (∃ φ : ℝ, IsExponential φ c) ∨ IsAffine c := by sorry

end HarksKlimm.Consistency
