-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_pt_bound
-- name    : GlobalTheory.CompanionTheory.SW.LatSum.pt_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:06:02.078519+00:00
-- url     : https://prove2.me/theorems/17910b91-531c-486a-a247-34206c857b7a
-- title:
--   Lat Sum: pt bound
-- statement:
--   The Lat Sum construction uses the pt bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L32-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L32-L52

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

theorem GlobalTheory.CompanionTheory.SW.LatSum.pt_bound {t u y : ℝ} (ht : 0 < t) (hy : t ≤ y) (hu : y ≤ u) (m : ℕ) :
    (u ^ (m + 2))⁻¹ ≤ (1 + 1 / t) * (y ^ m)⁻¹ * (1 / u - 1 / (u + 1)) := by sorry
