-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_RMulGram_colsM_rmul
-- name    : GlobalTheory.CompanionTheory.SW.RMulGram.colsM_rmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:35:13.761417+00:00
-- url     : https://prove2.me/theorems/04340a9a-0573-4998-97d9-d112da259567
-- title:
--   RMul Gram: cols M rmul
-- statement:
--   The RMul Gram construction uses the cols M rmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightMulActionLaws.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightMulActionLaws.lean#L37-L41

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

theorem GlobalTheory.CompanionTheory.SW.RMulGram.colsM_rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    colsM R (rmul R X g) = colsM R X * g := by sorry
