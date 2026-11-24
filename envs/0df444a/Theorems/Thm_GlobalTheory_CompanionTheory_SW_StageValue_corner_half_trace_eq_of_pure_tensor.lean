-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StageValue_corner_half_trace_eq_of_pure_tensor
-- name    : GlobalTheory.CompanionTheory.SW.StageValue.corner_half_trace_eq_of_pure_tensor
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:09:39.715112+00:00
-- url     : https://prove2.me/theorems/cd9012dd-6482-41a8-a6f6-5a22fbc0542c
-- title:
--   Stage Value: corner half trace eq of pure tensor
-- statement:
--   The Stage Value construction uses the corner half trace eq of pure tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductSupport.lean#L20-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductSupport.lean#L20-L34

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StageValue
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem GlobalTheory.CompanionTheory.SW.StageValue.corner_half_trace_eq_of_pure_tensor [CharZero F] (hfr : Module.finrank F E = 2) {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) {x : R}
    (h : S 0 0 = x ⊗ₜ[F] (1 : E)) : s0 R S = x := by sorry
