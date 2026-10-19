-- Prove2me | Theorems.Thm_MazurTransfer_cyclic_quotient_action_eq_character_smul
-- name    : MazurTransfer.cyclic_quotient_action_eq_character_smul
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T23:29:05.608473+00:00
-- url     : https://prove2.me/theorems/998f1ac8-ad83-4a97-a5ef-c47e4a4d89c1
-- statement:
--   For a linear representation factoring on a specified vector through a cyclic quotient, fixing by the quotient kernel and the scalar action of a generator lift determine the full character action. The original universes, fields, groups, modules, generator and vector hypotheses are unchanged.

import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic

noncomputable section
universe u v w x
variable {k : Type u} [Field k] {G : Type v} [Group G] {H : Type w} [Group H]
variable {V : Type x} [AddCommGroup V] [Module k V]

theorem MazurTransfer.cyclic_quotient_action_eq_character_smul
    (ρ : Representation k G V) (q : G →* H) (χ : H →* kˣ)
    (h : H) (hg : ∀ y : H, ∃ n : ℕ, y = h ^ n) (g : G) (hq : q g = h)
    (v : V) (hfix : ∀ s : G, q s = 1 → ρ s v = v)
    (hv : ρ g v = (χ h : k) • v) (s : G) :
    ρ s v = (χ (q s) : k) • v := by sorry
