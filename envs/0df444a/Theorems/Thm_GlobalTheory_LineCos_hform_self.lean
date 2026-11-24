-- Prove2me | Theorems.Thm_GlobalTheory_LineCos_hform_self
-- name    : GlobalTheory.LineCos.hform_self
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:07:24.278747+00:00
-- url     : https://prove2.me/theorems/3d0bf4fa-3764-4b59-a78d-7bbe620ebac6
-- title:
--   Line Cos: hform self
-- statement:
--   The Line Cos construction uses the hform self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOnCosSq.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOnCosSq.lean#L26-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LineCos

theorem GlobalTheory.LineCos.hform_self (G : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 2 → ℂ) :
    hform G a a = star (starRingEnd ℂ ∘ a) ⬝ᵥ (G *ᵥ (starRingEnd ℂ ∘ a)) := by sorry
