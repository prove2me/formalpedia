-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_GaussReg_posdef_quadratic_lower_bound_l1
-- name    : GlobalTheory.CompanionTheory.SW.BB.GaussReg.posdef_quadratic_lower_bound_l1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:10.85792+00:00
-- url     : https://prove2.me/theorems/3ad57aec-509c-4100-9736-5021924f2480
-- title:
--   Gauss Reg: posdef quadratic lower bound l1
-- statement:
--   The Gauss Reg construction uses the posdef quadratic lower bound l1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianContinuousRapidDecay.lean#L37-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianContinuousRapidDecay.lean#L37-L51

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

theorem GlobalTheory.CompanionTheory.SW.BB.GaussReg.posdef_quadratic_lower_bound_l1 {n : Type} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : n → ℝ, c * (∑ p, |x p|) ^ 2 ≤ x ⬝ᵥ (P *ᵥ x) := by sorry
