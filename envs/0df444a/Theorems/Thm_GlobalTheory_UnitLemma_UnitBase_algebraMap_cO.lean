-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnitBase_algebraMap_cO
-- name    : GlobalTheory.UnitLemma.UnitBase.algebraMap_cO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:34.660113+00:00
-- url     : https://prove2.me/theorems/62281e60-821b-4800-bb8a-b8b953464d33
-- title:
--   Unit Base: algebra Map c O
-- statement:
--   The Unit Base construction uses the algebra Map c O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean#L131-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean#L131-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnitBase
open GlobalTheory.UnitLemma Polynomial

theorem GlobalTheory.UnitLemma.UnitBase.algebraMap_cO (K : UQ) (x : K.O) : algebraMap K.O K.E (cO K x) = K.c (algebraMap K.O K.E x) := by sorry
