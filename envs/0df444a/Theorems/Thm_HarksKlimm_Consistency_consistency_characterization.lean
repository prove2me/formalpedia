-- Prove2me | Theorems.Thm_HarksKlimm_Consistency_consistency_characterization
-- name    : HarksKlimm.Consistency.consistency_characterization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:28.693988+00:00
-- url     : https://prove2.me/theorems/133d1934-2361-4db0-80ec-f8d47eecbfd2
-- title:
--   Theorem 5.1 — Characterization of universal pure-equilibrium existence
-- statement:
--   Let $C$ be any set of continuous real-valued functions on $[0,\infty)$. The following three conditions are equivalent: every finite weighted congestion game with facility costs in $C$ has a pure Nash equilibrium; every such game has the finite improvement property; and
--   $$\bigl(\forall c\in C\ \exists a_c,b_c\in\mathbb R\ \forall x\ge0,\ c(x)=a_cx+b_c\bigr)
--   \quad\text{or}\quad
--   \bigl(\exists\varphi\in\mathbb R\ \forall c\in C\ \exists a_c,b_c\in\mathbb R\ \forall x\ge0,\ c(x)=a_ce^{\varphi x}+b_c\bigr).$$
--   Thus a class guarantees universal equilibrium existence exactly when it guarantees termination of strict improvement paths, and precisely the displayed function classes have these properties.
--
--   **Formalization Note** The disjunction is inclusive, and $\varphi$ is chosen once for the whole class. The three-way equivalence is represented by two adjacent biconditionals. Games have positive real demands and arbitrary nonempty finite strategy families; private costs include the demand factor. Continuity is on the closed half-line. The class may be empty, costs may have either sign, and no rate or coefficient is required to be nonzero.
-- source:
--   Harks and Klimm (2012), https://doi.org/10.1287/moor.1120.0543, Theorem 5.1, p. 427 (PDF p. 9)

import Definitions.Def_HarksKlimm_Consistency_Consistent
import Definitions.Def_HarksKlimm_Consistency_FIPConsistent
import Definitions.Def_HarksKlimm_Consistency_IsAffine
import Definitions.Def_HarksKlimm_Consistency_IsExponential
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

namespace MondererShapley.ClosedPath

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}


def IsStep (a b : ∀ i, Y i) (i : ι) : Prop := b i ≠ a i ∧ ∀ j, j ≠ i → b j = a j

end MondererShapley.ClosedPath

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsStep

namespace MondererShapley.Improvement

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}


def HasFIP (u : ι → (∀ i, Y i) → ℝ) : Prop :=
  ¬ ∃ (y : ℕ → ∀ i, Y i) (d : ℕ → ι),
      ∀ k, MondererShapley.ClosedPath.IsStep (y k) (y (k + 1)) (d k) ∧
        u (d k) (y k) < u (d k) (y (k + 1))

end MondererShapley.Improvement

import Definitions.Def_HarksKlimm_Consistency_privateCost
import Definitions.Def_MondererShapley_Improvement_HasFIP
set_option autoImplicit false



namespace HarksKlimm.Consistency

def FIPConsistent (C : Set (ℝ≥0 → ℝ)) : Prop :=
  ∀ (n m : ℕ) (G : Game n m), (∀ f, G.cost f ∈ C) →
    MondererShapley.Improvement.HasFIP (fun i t => -privateCost G t i)

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

theorem consistency_characterization (C : Set (ℝ≥0 → ℝ))
    (hC : ∀ c ∈ C, Continuous c) :
    (Consistent C ↔ FIPConsistent C) ∧
    (FIPConsistent C ↔
      ((∀ c ∈ C, IsAffine c) ∨ (∃ φ : ℝ, ∀ c ∈ C, IsExponential φ c))) := by sorry

end HarksKlimm.Consistency
