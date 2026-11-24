-- Prove2me | Theorems.Thm_GlobalTheory_GradedFixed_comp_outside
-- name    : GlobalTheory.GradedFixed.comp_outside
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:13:06.82493+00:00
-- url     : https://prove2.me/theorems/df2b7638-9879-4cd8-bd45-4be7a197429d
-- title:
--   Graded Fixed: comp outside
-- statement:
--   The Graded Fixed construction uses the comp outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L107-L110

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
omit hc1 hc2 hc4

theorem GlobalTheory.GradedFixed.comp_outside {A : Set ι} {x : M} (hx : x ∈ WA V A) {l : ι} (hl : l ∉ A) : c l x = 0 := by sorry
