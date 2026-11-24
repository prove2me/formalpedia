-- Prove2me | Theorems.Thm_GlobalTheory_GradedFixed_fixed_part
-- name    : GlobalTheory.GradedFixed.fixed_part
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:53.708907+00:00
-- url     : https://prove2.me/theorems/1f07cf27-61fe-40e0-917b-a0c16c89b8e8
-- title:
--   Graded Fixed: fixed part
-- statement:
--   The Graded Fixed construction uses the fixed part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L44-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L44-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule MulAction
open GlobalTheory GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.GradedFixed.fixed_part (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (hV : iSupIndep V)
    (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) {A B : Set ι}
    (hA : ∀ (g : G), ∀ j ∈ A, g • j ∈ A) (hB : ∀ (g : G), ∀ j ∈ B, g • j ∈ B)
    (hAB : Disjoint A B) {a b : M} (ha : a ∈ WA V A) (hb : b ∈ WA V B)
    (hfix : ∀ g, π g (a + b) = a + b) : ∀ g, π g a = a := by sorry
