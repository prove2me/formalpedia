-- Prove2me | Theorems.Thm_GlobalTheory_JR_SuppBdd_isClosed_unitary_set
-- name    : GlobalTheory.JR.SuppBdd.isClosed_unitary_set
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:37:05.61863+00:00
-- url     : https://prove2.me/theorems/b2d1dd3c-e4fe-4d0a-a8a3-bb062d018f7a
-- title:
--   Supp Bdd: is Closed unitary set
-- statement:
--   The Supp Bdd construction uses the is Closed unitary set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompactUnitariesIntegralOrbitOfHankelDetNe.lean#L8-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompactUnitariesIntegralOrbitOfHankelDetNe.lean#L8-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactUnitariesIntegralOrbitOfHankelDetNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SuppBdd

theorem GlobalTheory.JR.SuppBdd.isClosed_unitary_set {n : ℕ} {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
    [StarRing E] [ContinuousStar E] :
    IsClosed ((Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E))) := by sorry
