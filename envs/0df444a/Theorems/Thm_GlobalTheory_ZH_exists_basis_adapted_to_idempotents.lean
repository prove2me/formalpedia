-- Prove2me | Theorems.Thm_GlobalTheory_ZH_exists_basis_adapted_to_idempotents
-- name    : GlobalTheory.ZH.exists_basis_adapted_to_idempotents
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:41.227497+00:00
-- url     : https://prove2.me/theorems/2472a2bf-cdd3-43c2-bd21-d1ee359871a2
-- title:
--   ZH: exists basis adapted to idempotents
-- statement:
--   The ZH construction uses the exists basis adapted to idempotents property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisAdaptedToIdempotents.lean#L23-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisAdaptedToIdempotents.lean#L23-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedToIdempotents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.ZH
open Module

theorem GlobalTheory.ZH.exists_basis_adapted_to_idempotents :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (J C : Type) [Fintype J] [DecidableEq J] [Fintype C]
      [DecidableEq C] (e : C → Matrix J J O),
      (∀ c c', e c * e c' = if c = c' then e c else 0) → ∑ c, e c = 1 →
      ∃ (κ : J → C) (col : J → J),
        IsUnit (Matrix.det (Matrix.of fun i j => e (κ i) j (col i))) ∧
        ∀ c, Submodule.span O (Set.range fun i => fun j => e c j i) =
          Submodule.span O {v | ∃ i, κ i = c ∧ v = fun j => e c j (col i)} := by sorry
