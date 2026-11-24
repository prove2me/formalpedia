-- Prove2me | Theorems.Thm_GlobalTheory_EntireFunctionHalfPlane_entire_eq_of_eqOn_halfPlane
-- name    : GlobalTheory.EntireFunctionHalfPlane.entire_eq_of_eqOn_halfPlane
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:57:44.962797+00:00
-- url     : https://prove2.me/theorems/90867f82-70ad-4dcb-8e96-b64d2d3526b4
-- title:
--   Entire Function Half Plane: entire eq of eq On half Plane
-- statement:
--   The Entire Function Half Plane construction uses the entire eq of eq On half Plane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EntireEqOfEqOnHalfPlane.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EntireEqOfEqOnHalfPlane.lean#L7-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EntireFunctionHalfPlane
open Filter Topology

theorem GlobalTheory.EntireFunctionHalfPlane.entire_eq_of_eqOn_halfPlane {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (a : ℝ) (h : ∀ s : ℂ, a < s.re → f s = g s) : f = g := by sorry
