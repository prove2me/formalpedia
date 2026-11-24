-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_RMulGram_rmul_rmul
-- name    : GlobalTheory.CompanionTheory.SW.RMulGram.rmul_rmul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:10:05.167347+00:00
-- url     : https://prove2.me/theorems/09b03842-bb88-4cbd-aecf-2f910c933dc2
-- title:
--   RMul Gram: rmul rmul
-- statement:
--   The RMul Gram construction uses the rmul rmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightMulActionLaws.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightMulActionLaws.lean#L49-L53

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightMulActionLaws
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RMulGram
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem GlobalTheory.CompanionTheory.SW.RMulGram.rmul_rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (rmul R X g) g' = rmul R X (g * g') := by sorry
