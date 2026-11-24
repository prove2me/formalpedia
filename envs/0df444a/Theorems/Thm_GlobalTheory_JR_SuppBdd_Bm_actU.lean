-- Prove2me | Theorems.Thm_GlobalTheory_JR_SuppBdd_Bm_actU
-- name    : GlobalTheory.JR.SuppBdd.Bm_actU
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:38:37.160354+00:00
-- url     : https://prove2.me/theorems/8ddd975d-9772-4a04-9799-ab6481089075
-- title:
--   Supp Bdd: Bm act U
-- statement:
--   The Supp Bdd construction uses the Bm act U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompactUnitariesIntegralOrbitOfHankelDetNe.lean#L30-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompactUnitariesIntegralOrbitOfHankelDetNe.lean#L30-L42

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

theorem GlobalTheory.JR.SuppBdd.Bm_actU {n : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    (g : Matrix.unitaryGroup (Fin n) E) (Y : Hn n F E) :
    Bm (actU g Y).toGl = g.1 * Bm Y.toGl := by sorry
