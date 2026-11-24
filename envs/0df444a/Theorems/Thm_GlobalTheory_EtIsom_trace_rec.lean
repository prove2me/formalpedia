-- Prove2me | Theorems.Thm_GlobalTheory_EtIsom_trace_rec
-- name    : GlobalTheory.EtIsom.trace_rec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:12:34.18405+00:00
-- url     : https://prove2.me/theorems/11155dd3-5ef1-437a-a44f-2ee4ff8bc1dc
-- title:
--   Et Isom: trace rec
-- statement:
--   The Et Isom construction uses the trace rec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L185-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean#L185-L191

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem GlobalTheory.EtIsom.trace_rec (hG : A.IsGen τ p) (a : A.K) (m : ℕ) :
    algebraMap F E (Algebra.trace F A.K (τ ^ (m + r) * a)) =
      -∑ i, algebraMap F E (p i) • algebraMap F E (Algebra.trace F A.K (τ ^ (m + (i : ℕ)) * a)) := by sorry
