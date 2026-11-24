-- Prove2me | Theorems.Thm_GlobalTheory_GradedFixed_comp_equivariant
-- name    : GlobalTheory.GradedFixed.comp_equivariant
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:56:47.209814+00:00
-- url     : https://prove2.me/theorems/74cf95e6-72b4-4244-9fba-dd0b30c4833c
-- title:
--   Graded Fixed: comp equivariant
-- statement:
--   The Graded Fixed construction uses the comp equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L94-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L94-L104

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
variable (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (c : ι → M →ₗ[ℂ] M)
  (hc1 : ∀ i w, c i w ∈ V i) (hc2 : ∀ i v, v ∈ V i → c i v = v)
  (hc3 : ∀ i j v, i ≠ j → v ∈ V j → c i v = 0) (hc4 : ∀ w, ∃ F : Finset ι, w = ∑ i ∈ F, c i w)
include hc1 hc2 hc3 hc4

theorem GlobalTheory.GradedFixed.comp_equivariant (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i))
    (g : G) (i : ι) (w : M) : c (g • i) (π g w) = π g (c i w) := by sorry
