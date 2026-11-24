-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_GaussReg_exists_lower_sup
-- name    : GlobalTheory.CompanionTheory.SW.BB.GaussReg.exists_lower_sup
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:24.295929+00:00
-- url     : https://prove2.me/theorems/06576ef8-5008-41d5-9bb5-db922858e312
-- title:
--   Gauss Reg: exists lower sup
-- statement:
--   The Gauss Reg construction uses the exists lower sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianContinuousRapidDecay.lean#L10-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianContinuousRapidDecay.lean#L10-L35

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianContinuousRapidDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.GaussReg

theorem GlobalTheory.CompanionTheory.SW.BB.GaussReg.exists_lower_sup {n : Type} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : n → ℝ, c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (P *ᵥ x) := by sorry
