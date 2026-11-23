-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_isReduced_of_separable_P
-- name    : GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:39.914812+00:00
-- url     : https://prove2.me/theorems/0082e02e-62b0-4463-8fb6-6c205532f9f3
-- title:
--   Inv Alg: is Reduced of separable P
-- statement:
--   The Inv Alg construction uses the is Reduced of separable P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsReducedOfSeparableMarkedCharpoly.lean#L9-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsReducedOfSeparableMarkedCharpoly.lean#L9-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial

theorem GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsReduced B.A := by sorry
