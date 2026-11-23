-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_mulVec_first
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.mulVec_first
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:08.070849+00:00
-- url     : https://prove2.me/theorems/8a7e545d-a6b4-4348-8f45-46191261c035
-- title:
--   Stab First: mul Vec first
-- statement:
--   The Stab First construction uses the mul Vec first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L140-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L140-L142

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {K : Type} [CommRing K] {M : ℕ}

theorem GlobalTheory.CompanionTheory.SW.StabFirst.mulVec_first (A : Matrix (Fin (M + 1)) (Fin (M + 1)) K) (a : Fin (M + 1)) :
    A.mulVec (Fin.cons 1 (fun _ => 0)) a = A a 0 := by sorry
