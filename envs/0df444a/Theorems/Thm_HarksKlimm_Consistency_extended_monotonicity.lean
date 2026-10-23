-- Prove2me | Theorems.Thm_HarksKlimm_Consistency_extended_monotonicity
-- name    : HarksKlimm.Consistency.extended_monotonicity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:22.108209+00:00
-- url     : https://prove2.me/theorems/778d9a7e-60c0-4306-97cc-0f640809d651
-- title:
--   Lemma 3.4 — Extended Monotonicity Lemma
-- statement:
--   Let $C$ be a set of continuous cost functions on $[0,\infty)$. If every weighted congestion game with costs in $C$ admits a pure Nash equilibrium, then
--   $$\forall h\in\mathcal L_{\mathbb Z}(C),\quad h\text{ is nondecreasing or nonincreasing}.$$
--   Here $\mathcal L_{\mathbb Z}(C)$ consists of all finite integer combinations of nonnegative translates of members of $C$. This is a necessary analytic condition for universal equilibrium existence.
--
--   **Formalization Note** Consistency is unrestricted in the number of players. Continuity includes zero; neither the class nor its costs have a positivity requirement.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, Lemma 3.4 (Extended Monotonicity Lemma), p. 424 (PDF p. 6)

import Definitions.Def_HarksKlimm_Consistency_Consistent
import Definitions.Def_HarksKlimm_Consistency_IntegerHull
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

def Consistent (C : Set (ℝ≥0 → ℝ)) : Prop :=
  ∀ (n m : ℕ) (G : Game n m), (∀ f, G.cost f ∈ C) →
    ∃ s : G.Profile, AGT.IsPureNash (fun i t => -privateCost G t i) s

end HarksKlimm.Consistency

import Mathlib
set_option autoImplicit false

namespace HarksKlimm.Consistency

def IntegerHull (C : Set (ℝ≥0 → ℝ)) : Set (ℝ≥0 → ℝ) :=
  {h | ∃ (K : ℕ) (a : Fin K → ℤ) (b : Fin K → ℝ≥0)
      (c : Fin K → ℝ≥0 → ℝ),
    (∀ k, c k ∈ C) ∧ ∀ x, h x = ∑ k : Fin K, (a k : ℝ) * c k (x + b k)}

end HarksKlimm.Consistency

import Mathlib
set_option autoImplicit false

namespace HarksKlimm.Consistency

def IsMonotonic (c : ℝ≥0 → ℝ) : Prop := Monotone c ∨ Antitone c

end HarksKlimm.Consistency
-/

namespace HarksKlimm.Consistency

theorem extended_monotonicity (C : Set (ℝ≥0 → ℝ))
    (hC : ∀ c ∈ C, Continuous c) (hcons : Consistent C) :
    ∀ h ∈ IntegerHull C, IsMonotonic h := by sorry

end HarksKlimm.Consistency
