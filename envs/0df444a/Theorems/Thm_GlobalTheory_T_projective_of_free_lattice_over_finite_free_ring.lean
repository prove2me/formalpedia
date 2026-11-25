-- Prove2me | Theorems.Thm_GlobalTheory_T_projective_of_free_lattice_over_finite_free_ring
-- name    : GlobalTheory.T.projective_of_free_lattice_over_finite_free_ring
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:53.095594+00:00
-- url     : https://prove2.me/theorems/323a585c-2c06-44e9-94b4-b223252f2aaf
-- title:
--   T: projective of free lattice over finite free ring
-- statement:
--   The T construction uses the projective of free lattice over finite free ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProjectiveOfFreeLatticeOverFiniteFreeRingStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProjectiveOfFreeLatticeOverFiniteFreeRingStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProjectiveOfFreeLatticeOverFiniteFreeRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProjectiveOfFreeLatticeOverFiniteFreeRingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.projective_of_free_lattice_over_finite_free_ring : ∀ (Z S A D : Type) [CommRing Z] [CommRing S] [CommRing A] [AddCommGroup D] [Module A D] (z : Z →+* S) (a : S →+* A) (N : Submodule A D) (q : ℕ) (x : Fin q → D), (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → (∀ s : Fin q → S, ∑ i, a (s i) • x i = 0 → s = 0) → (∃ (d : ℕ) (w : Fin d → S), ∀ y : S, ∃! c : Fin d → Z, y = ∑ i, z (c i) * w i) → @Module.Projective Z _ ↥N _ (Module.compHom _ (a.comp z)) := by sorry
