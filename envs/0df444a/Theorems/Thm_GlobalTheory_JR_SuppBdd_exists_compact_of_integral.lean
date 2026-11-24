-- Prove2me | Theorems.Thm_GlobalTheory_JR_SuppBdd_exists_compact_of_integral
-- name    : GlobalTheory.JR.SuppBdd.exists_compact_of_integral
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:38:07.729966+00:00
-- url     : https://prove2.me/theorems/fbdf7a4f-f02a-4bcd-ada1-7fd71ecc4dc7
-- title:
--   Supp Bdd: exists compact of integral
-- statement:
--   The Supp Bdd construction uses the exists compact of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompactUnitariesIntegralOrbitOfHankelDetNe.lean#L44-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompactUnitariesIntegralOrbitOfHankelDetNe.lean#L44-L83

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

theorem GlobalTheory.JR.SuppBdd.exists_compact_of_integral : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] {n : ℕ} (Y : Hn n F E), Delta (inv Y.toGl) ≠ 0 →
    ∃ K : Set (Matrix.unitaryGroup (Fin n) E), IsCompact K ∧ ∀ g, unitU n F E (actU g Y) ≠ 0 → g ∈ K := by sorry
