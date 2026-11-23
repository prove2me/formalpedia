-- Prove2me | Theorems.Thm_GlobalTheory_QFam_eis_hasQ_int
-- name    : GlobalTheory.QFam.eis_hasQ_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:18.199774+00:00
-- url     : https://prove2.me/theorems/c3d3ae97-08ad-44f9-8c25-876ae39e8568
-- title:
--   QFam: eis has Q int
-- statement:
--   The QFam construction uses the eis has Q int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EisensteinDeltaQExpansionIntegrality.lean#L46-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EisensteinDeltaQExpansionIntegrality.lean#L46-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EisensteinDeltaQExpansionIntegrality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.eis_hasQ_int (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ) (hF : F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) :
    ∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ) := by sorry
