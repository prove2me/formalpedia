-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_GaussReg_exists_lower_family
-- name    : GlobalTheory.CompanionTheory.SW.BB.GaussReg.exists_lower_family
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:02:14.174363+00:00
-- url     : https://prove2.me/theorems/8eeb8752-bce8-4517-ab5b-fd4dafbbd4b6
-- title:
--   Gauss Reg: exists lower family
-- statement:
--   The Gauss Reg construction uses the exists lower family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianContinuousRapidDecay.lean#L53-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianContinuousRapidDecay.lean#L53-L76

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

theorem GlobalTheory.CompanionTheory.SW.BB.GaussReg.exists_lower_family {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n]
    {P : ι → Matrix n n ℝ} (hP : ∀ i, (P i).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ι → n → ℝ,
      c * (∑ i, ∑ p, |y i p|) ^ 2 ≤ ∑ i, y i ⬝ᵥ (P i *ᵥ y i) := by sorry
