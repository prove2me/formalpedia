-- Prove2me | Theorems.Thm_GlobalTheory_QFam_HasQ_fun_unique
-- name    : GlobalTheory.QFam.HasQ.fun_unique
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:55.498393+00:00
-- url     : https://prove2.me/theorems/4685121f-77c3-4641-80a5-3e578999fb24
-- title:
--   Has Q: fun unique
-- statement:
--   The Has Q construction uses the fun unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelCoeffAndFunctionUnique.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelCoeffAndFunctionUnique.lean#L21-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelCoeffAndFunctionUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.HasQ.fun_unique {N : ℕ} {f g : ℍ → ℂ} {a : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g a) :
    f = g := by sorry
