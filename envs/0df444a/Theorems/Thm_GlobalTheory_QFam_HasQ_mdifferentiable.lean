-- Prove2me | Theorems.Thm_GlobalTheory_QFam_HasQ_mdifferentiable
-- name    : GlobalTheory.QFam.HasQ.mdifferentiable
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:18:52.062891+00:00
-- url     : https://prove2.me/theorems/fd17e477-b69a-45ac-be25-1e20b8a31bf8
-- title:
--   Has Q: mdifferentiable
-- statement:
--   The Has Q construction uses the mdifferentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQMdifferentiableAndIsBoundedAtImInfty.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQMdifferentiableAndIsBoundedAtImInfty.lean#L12-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQCoeffIffHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQMdifferentiableAndIsBoundedAtImInfty
import Theorems.Thm_GlobalTheory_HasQExpansion_mdifferentiable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

theorem GlobalTheory.QFam.HasQ.mdifferentiable {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (hN : 0 < N)
    (h : _root_.GlobalTheory.QFam.HasQ N f a) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by sorry
