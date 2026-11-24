-- Prove2me | Theorems.Thm_GlobalTheory_QFam_HasQ_isBoundedAtImInfty
-- name    : GlobalTheory.QFam.HasQ.isBoundedAtImInfty
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:58:32.455077+00:00
-- url     : https://prove2.me/theorems/8f4c1db1-b65c-4d63-a5b8-23ca2ff7ec3a
-- title:
--   Has Q: is Bounded At Im Infty
-- statement:
--   The Has Q construction uses the is Bounded At Im Infty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQMdifferentiableAndIsBoundedAtImInfty.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQMdifferentiableAndIsBoundedAtImInfty.lean#L19-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQCoeffIffHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQMdifferentiableAndIsBoundedAtImInfty
import Theorems.Thm_GlobalTheory_HasQExpansion_isBoundedAtImInfty

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

theorem GlobalTheory.QFam.HasQ.isBoundedAtImInfty {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (hN : 0 < N) (h : HasQ N f a) :
    UpperHalfPlane.IsBoundedAtImInfty f := by sorry
