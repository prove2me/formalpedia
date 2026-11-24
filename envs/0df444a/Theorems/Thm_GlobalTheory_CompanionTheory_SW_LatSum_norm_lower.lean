-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_norm_lower
-- name    : GlobalTheory.CompanionTheory.SW.LatSum.norm_lower
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:06:58.118406+00:00
-- url     : https://prove2.me/theorems/e576504f-a371-4432-a135-33eb29368ddb
-- title:
--   Lat Sum: norm lower
-- statement:
--   The Lat Sum construction uses the norm lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L96-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L96-L121

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EisensteinLatticeSumBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatSum

theorem GlobalTheory.CompanionTheory.SW.LatSum.norm_lower {t : ℝ} (ht : 0 < t) (z : ℂ) (hz : t ≤ z.im) (s : ℝ) :
    (2 + 1 / t)⁻¹ * (|((⌊z.re + s⌋ : ℤ) : ℝ)| + z.im) ≤ ‖z + (s : ℂ)‖ := by sorry
