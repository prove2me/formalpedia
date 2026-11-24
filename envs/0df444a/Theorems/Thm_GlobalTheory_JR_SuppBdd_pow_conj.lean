-- Prove2me | Theorems.Thm_GlobalTheory_JR_SuppBdd_pow_conj
-- name    : GlobalTheory.JR.SuppBdd.pow_conj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:38:14.362578+00:00
-- url     : https://prove2.me/theorems/4e9250c9-9ec6-483d-983e-5f53ff55057f
-- title:
--   Supp Bdd: pow conj
-- statement:
--   The Supp Bdd construction uses the pow conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompactUnitariesIntegralOrbitOfHankelDetNe.lean#L18-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompactUnitariesIntegralOrbitOfHankelDetNe.lean#L18-L28

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

theorem GlobalTheory.JR.SuppBdd.pow_conj {n : ℕ} {E : Type} [CommRing E] [StarRing E] (g : Matrix.unitaryGroup (Fin n) E)
    (A : Matrix (Fin n) (Fin n) E) (j : ℕ) : (g.1 * A * star g.1) ^ j = g.1 * A ^ j * star g.1 := by sorry
