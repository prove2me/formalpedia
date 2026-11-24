-- Prove2me | Theorems.Thm_GlobalTheory_JR_ResidueGauss_algebraMap_continuous_isCompact_preimage
-- name    : GlobalTheory.JR.ResidueGauss.algebraMap_continuous_isCompact_preimage
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:36:26.535659+00:00
-- url     : https://prove2.me/theorems/b4aa8f45-fea3-489c-8f77-9cf35c428e4f
-- title:
--   Residue Gauss: algebra Map continuous is Compact preimage
-- statement:
--   The Residue Gauss construction uses the algebra Map continuous is Compact preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidueGaussIntegralNormForm.lean#L84-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidueGaussIntegralNormForm.lean#L84-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGaussIntegralNormForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ResidueGauss

theorem GlobalTheory.JR.ResidueGauss.algebraMap_continuous_isCompact_preimage {F E : Type} [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [U : Unram F E] (A : Et F E) :
    Continuous (algebraMap A.K A.L) ∧
      ∀ O : Set A.L, IsCompact O → IsCompact (algebraMap A.K A.L ⁻¹' O) := by sorry
