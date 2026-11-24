-- Prove2me | Theorems.Thm_GlobalTheory_QFam_hasQ_mdifferentiable_and_isBoundedAtImInfty
-- name    : GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:14.803698+00:00
-- url     : https://prove2.me/theorems/f3609aa0-154f-4835-9267-56979a3b38d5
-- title:
--   QFam: has Q mdifferentiable and is Bounded At Im Infty
-- statement:
--   The QFam construction uses the has Q mdifferentiable and is Bounded At Im Infty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQMdifferentiableAndIsBoundedAtImInfty.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQMdifferentiableAndIsBoundedAtImInfty.lean#L25-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQCoeffIffHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQMdifferentiableAndIsBoundedAtImInfty
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

theorem GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty :
    ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → _root_.GlobalTheory.QFam.HasQ N f a →
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ UpperHalfPlane.IsBoundedAtImInfty f := by sorry
