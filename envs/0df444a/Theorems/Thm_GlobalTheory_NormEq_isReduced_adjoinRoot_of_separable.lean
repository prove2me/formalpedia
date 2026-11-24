-- Prove2me | Theorems.Thm_GlobalTheory_NormEq_isReduced_adjoinRoot_of_separable
-- name    : GlobalTheory.NormEq.isReduced_adjoinRoot_of_separable
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:34:59.021132+00:00
-- url     : https://prove2.me/theorems/4ee39017-4898-4ad0-b91e-176940ea780c
-- title:
--   Norm Eq: is Reduced adjoin Root of separable
-- statement:
--   The Norm Eq construction uses the is Reduced adjoin Root of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormApproximationFirstLevel.lean#L214-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormApproximationFirstLevel.lean#L214-L222

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulInvolEqOfFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedAdjoinRootOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFirstLevel
import Theorems.Thm_GlobalTheory_ReducedAdjoinRootSeparable_isReduced_adjoinRoot_of_separable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.NormEq.isReduced_adjoinRoot_of_separable {k : Type} [Field k] {f : k[X]} (hf : f.Separable) :
    IsReduced (AdjoinRoot f) := by sorry
