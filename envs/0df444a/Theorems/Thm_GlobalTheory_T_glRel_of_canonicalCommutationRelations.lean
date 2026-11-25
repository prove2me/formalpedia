-- Prove2me | Theorems.Thm_GlobalTheory_T_glRel_of_canonicalCommutationRelations
-- name    : GlobalTheory.T.glRel_of_canonicalCommutationRelations
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:34.705806+00:00
-- url     : https://prove2.me/theorems/e075205b-8e95-524a-98a2-8532366018f6
-- title:
--   T: gl Rel of canonical Commutation Relations
-- statement:
--   The T construction uses the gl Rel of canonical Commutation Relations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlRelOfCanonicalCommutationRelationsStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlRelOfCanonicalCommutationRelationsStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlRelOfCanonicalCommutationRelations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlRelOfCanonicalCommutationRelationsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.Mem.Lift
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.glRel_of_canonicalCommutationRelations : ∀ (A : Type) [Ring A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → Formalism.REAL.GlRel (fun i j : Fin n => ∑ a, x (i, a) * d (j, a)) ∧ Formalism.REAL.GlRel (fun a b : Fin m => -∑ i, x (i, b) * d (i, a)) := by sorry
