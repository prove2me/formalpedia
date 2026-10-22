-- Prove2me | Theorems.Thm_HarksKlimm_Consistency_restricted_hulls_monotonic
-- name    : HarksKlimm.Consistency.restricted_hulls_monotonic
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:47:57.246388+00:00
-- url     : https://prove2.me/theorems/31f23f7c-497b-49cd-a8d5-ebf87f78c7cb
-- title:
--   Proposition 5.1 — Two restricted integer hulls
-- statement:
--   Let $C$ be a class of continuous functions on $[0,\infty)$ that is consistent for exactly three-player weighted congestion games. Then
--   $$\bigl(\forall h\in\mathcal L_{\mathbb Z}^2(C),\ h\text{ is monotonic}\bigr)\quad\text{and}\quad
--   \bigl(\forall h\in\mathcal L_{\mathbb Z}^3(C),\ h\text{ is monotonic}\bigr).$$
--   The first hull uses two possibly different functions without shifts; the second uses one function and its strictly positive translate. Monotonic means nondecreasing or nonincreasing for each function separately.
--
--   **Formalization Note** Both hulls use integer coefficients. The hypothesis quantifies over all three-player games, not a particular construction.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, Proposition 5.1, p. 426 (PDF p. 8)

import Definitions.Def_HarksKlimm_Consistency_ThreeConsistent
import Definitions.Def_HarksKlimm_Consistency_TwoHull
import Definitions.Def_HarksKlimm_Consistency_ShiftHull
import Definitions.Def_HarksKlimm_Consistency_IsMonotonic
set_option autoImplicit false
open scoped NNReal

/- Imported Lean declaration context (code only; not new declarations):

import Mathlib
set_option autoImplicit false

namespace HarksKlimm.Consistency

structure Game (n m : ℕ) where
  players_pos : 0 < n
  facilities_pos : 0 < m
  strategies : Fin n → Finset (Finset (Fin m))
  strategies_nonempty : ∀ i, (strategies i).Nonempty
  demand : Fin n → ℝ≥0
  demand_pos : ∀ i, 0 < demand i
  cost : Fin m → ℝ≥0 → ℝ

abbrev Game.Strategy {n m : ℕ} (G : Game n m) (i : Fin n) :=
  ↥(G.strategies i)

abbrev Game.Profile {n m : ℕ} (G : Game n m) :=
  ∀ i, G.Strategy i

end HarksKlimm.Consistency

import Definitions.Def_HarksKlimm_Consistency_Game
set_option autoImplicit false



namespace HarksKlimm.Consistency

noncomputable def load {n m : ℕ} (G : Game n m) (s : G.Profile)
    (f : Fin m) : ℝ≥0 :=
  ∑ j : Fin n, if f ∈ (s j).val then G.demand j else 0

end HarksKlimm.Consistency

import Definitions.Def_HarksKlimm_Consistency_load
set_option autoImplicit false



namespace HarksKlimm.Consistency

noncomputable def privateCost {n m : ℕ} (G : Game n m) (s : G.Profile)
    (i : Fin n) : ℝ :=
  ∑ f ∈ (s i).val, (G.demand i : ℝ) * G.cost f (load G s f)

end HarksKlimm.Consistency

namespace AGT
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)]
def IsPureNash (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : Prop :=
  ∀ i (t : S i), u i (Function.update s i t) ≤ u i s
end AGT

import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_agt_games
set_option autoImplicit false



namespace HarksKlimm.Consistency

def ThreeConsistent (C : Set (ℝ≥0 → ℝ)) : Prop :=
  ∀ (m : ℕ) (G : Game 3 m), (∀ f, G.cost f ∈ C) →
    ∃ s : G.Profile, AGT.IsPureNash (fun i t => -privateCost G t i) s

end HarksKlimm.Consistency

import Mathlib
set_option autoImplicit false

namespace HarksKlimm.Consistency

def TwoHull (C : Set (ℝ≥0 → ℝ)) : Set (ℝ≥0 → ℝ) :=
  {h | ∃ (a₁ a₂ : ℤ) (c₁ c₂ : ℝ≥0 → ℝ),
    c₁ ∈ C ∧ c₂ ∈ C ∧ ∀ x, h x = (a₁ : ℝ) * c₁ x + (a₂ : ℝ) * c₂ x}

end HarksKlimm.Consistency

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
-/

namespace HarksKlimm.Consistency

theorem restricted_hulls_monotonic (C : Set (ℝ≥0 → ℝ))
    (hC : ∀ c ∈ C, Continuous c) (hcons : ThreeConsistent C) :
    (∀ h ∈ TwoHull C, IsMonotonic h) ∧
    (∀ h ∈ ShiftHull C, IsMonotonic h) := by sorry

end HarksKlimm.Consistency
