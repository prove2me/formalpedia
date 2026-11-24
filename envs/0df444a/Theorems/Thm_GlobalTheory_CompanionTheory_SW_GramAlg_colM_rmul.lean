-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_colM_rmul
-- name    : GlobalTheory.CompanionTheory.SW.GramAlg.colM_rmul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:05:40.127591+00:00
-- url     : https://prove2.me/theorems/c0f98098-0ac3-4248-9ca7-d74a158ec5d3
-- title:
--   Gram Alg: col M rmul
-- statement:
--   The Gram Alg construction uses the col M rmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightActionIdentities.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightActionIdentities.lean#L67-L70

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
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
variable {M n : ℕ}

theorem GlobalTheory.CompanionTheory.SW.GramAlg.colM_rmul (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    colM (rmul R X g) = colM X * g := by sorry
