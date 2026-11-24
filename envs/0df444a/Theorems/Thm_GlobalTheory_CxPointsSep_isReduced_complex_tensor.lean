-- Prove2me | Theorems.Thm_GlobalTheory_CxPointsSep_isReduced_complex_tensor
-- name    : GlobalTheory.CxPointsSep.isReduced_complex_tensor
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:32:45.396451+00:00
-- url     : https://prove2.me/theorems/534cb1dd-cd8f-43eb-9fc0-7732a46248bf
-- title:
--   Cx Points Sep: is Reduced complex tensor
-- statement:
--   The Cx Points Sep construction uses the is Reduced complex tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfForallAlgHom.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfForallAlgHom.lean#L29-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfForallAlgHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CxPointsSep

theorem GlobalTheory.CxPointsSep.isReduced_complex_tensor (D : Type) [CommRing D] [IsDomain D] [Algebra ℚ D]
    [Algebra.FiniteType ℚ D] : IsReduced (ℂ ⊗[ℚ] D) := by sorry
