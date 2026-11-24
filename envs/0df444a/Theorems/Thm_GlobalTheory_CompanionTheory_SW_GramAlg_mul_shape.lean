-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_mul_shape
-- name    : GlobalTheory.CompanionTheory.SW.GramAlg.mul_shape
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:05:27.472836+00:00
-- url     : https://prove2.me/theorems/07368a8d-e3a9-4daa-a4fe-1bdab9d39c43
-- title:
--   Gram Alg: mul shape
-- statement:
--   The Gram Alg construction uses the mul shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightActionIdentities.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightActionIdentities.lean#L27-L31

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramAlg
variable {A : Type} [CommRing A] {M n : ℕ}

theorem GlobalTheory.CompanionTheory.SW.GramAlg.mul_shape {p q r s t u : Type} [Fintype q] [Fintype r] [Fintype s] [Fintype t]
    (a : Matrix p q A) (b : Matrix q r A) (c : Matrix r s A) (d : Matrix s t A) (e : Matrix t u A) :
    (((a * b : Matrix p r A) * c : Matrix p s A) * (d * e : Matrix s u A) : Matrix p u A) =
      ((a * ((b * c : Matrix q s A) * d : Matrix q t A) : Matrix p t A) * e : Matrix p u A) := by sorry
