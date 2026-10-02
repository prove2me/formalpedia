-- Prove2me | Theorems.Thm_Glauberman_Dickson_h826_cyclic_family_shape
-- name    : Glauberman.Dickson.h826_cyclic_family_shape
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T13:42:09.583615+00:00
-- url     : https://prove2.me/theorems/cd93f360-bf04-40d3-90aa-7c2c45f02ada
-- title:
--   The one-normalizer or two-cyclic-family counting alternative
-- statement:
--   For a finite group H, suppose at most three cyclic-family size/index terms satisfy the displayed punctured-partition count and normalizer multiplier identities, with each multiplier between 1 and 2. A distinguished family has index relation determined by Q>1. Under the explicit term bounds in the formal statement, either the distinguished normalizer subgroup is all of H by cardinality, or exactly two families occur and both multipliers are 2. This is the finite counting consequence used in the large-Sylow-normalizer branch of Dickson classification.
-- source:
--   Qiuzhen-CFSG/CFSG, Glauberman/DicksonClassification.lean, hpre_shape in Huppert II.8.26; commit 96b2a02085dc678f3e0a97b334c31ada599c55fd, Apache-2.0. https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonClassification.lean . Original authorship preserved. arexychen: extraction, explicit parameterization, target-environment replay and validation.

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
set_option autoImplicit false
universe u

theorem Glauberman.Dickson.h826_cyclic_family_shape {H : Type u} [Group H] [Finite H]
    (Q r : ℕ) (NP : Subgroup H) (Z NZ : Fin r → Subgroup H)
    (s term : Fin r → ℕ) (i0 : Fin r)
    (hpm_gt : 1 < Q) (hfamily_bound : r ≤ 3)
    (hnontrivial : ∀ j, 1 < Nat.card (Z j))
    (hs : ∀ j, 1 ≤ s j ∧ s j ≤ 2)
    (hpartition_count : Nat.card H = 1 + (Q - 1) * NP.index + ∑ j, term j)
    (hz_index_factor : ∀ j, (Nat.card (Z j) * s j) * (NZ j).index = Nat.card H)
    (hterm_factor : ∀ j, term j + (NZ j).index = Nat.card (Z j) * (NZ j).index)
    (hterm_bound : ∀ j, Nat.card H ≤ 4 * term j)
    (hNP_index_factor : (Q * Nat.card (Z i0)) * NP.index = Nat.card H) :
    Nat.card H = Nat.card NP ∨ (r = 2 ∧ ∀ j, s j = 2) := by sorry
