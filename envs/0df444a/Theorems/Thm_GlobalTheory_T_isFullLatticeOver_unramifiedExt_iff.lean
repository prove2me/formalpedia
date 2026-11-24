-- Prove2me | Theorems.Thm_GlobalTheory_T_isFullLatticeOver_unramifiedExt_iff
-- name    : GlobalTheory.T.isFullLatticeOver_unramifiedExt_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:14.74605+00:00
-- url     : https://prove2.me/theorems/a8d3ed8a-9bc6-4c86-a1ef-ed8e32ce37ae
-- title:
--   T: is Full Lattice Over unramified Ext iff
-- statement:
--   The T construction uses the is Full Lattice Over unramified Ext iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsFullLatticeOverUnramifiedExtIffStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsFullLatticeOverUnramifiedExtIffStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeOverUnramifiedExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeOverUnramifiedExtIffStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isFullLatticeOver_unramifiedExt_iff : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (M : Submodule K.O B.A), (L : Set (overExt φ B ψ hψ hσ).A) = (M : Set B.A) → (IsLat K'.O K'.E L ↔ IsLat K.O K.E M) := by sorry
