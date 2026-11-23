-- Prove2me | Theorems.Thm_GlobalTheory_QFam_HasQ_sub
-- name    : GlobalTheory.QFam.HasQ.sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:33.548228+00:00
-- url     : https://prove2.me/theorems/4b1c10b3-1ba1-4e32-9910-91dc89bb5cae
-- title:
--   Has Q: sub
-- statement:
--   The Has Q construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelLinearOperations.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelLinearOperations.lean#L13-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
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

theorem GlobalTheory.QFam.HasQ.sub {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ - g τ) (fun n => a n - b n) := by sorry
