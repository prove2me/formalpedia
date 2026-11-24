-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Red_balanced_lower
-- name    : GlobalTheory.CompanionTheory.SW.Red.balanced_lower
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:08:37.30282+00:00
-- url     : https://prove2.me/theorems/c459d762-8fc6-4a13-b9b6-552f07262cfc
-- title:
--   Red: balanced lower
-- statement:
--   The Red construction uses the balanced lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ReductionToSiegelDomain.lean#L30-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ReductionToSiegelDomain.lean#L30-L53

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCuspReductionBoundStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MobiusActionUpperHalfPlaneStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CuspRepresentativesFiniteStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitBalancingImaginaryPartsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ReductionToSiegelDomain
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Red

theorem GlobalTheory.CompanionTheory.SW.Red.balanced_lower {ι : Type} [Fintype ι] (z : ι → ℝ) (hz : ∀ i, 0 < z i) (κ P : ℝ)
    (hκ : 0 < κ) (hbal : ∀ v w, κ * z w ≤ z v) (hprod : P ≤ ∏ i, z i) (w : ι) :
    κ * min 1 P ≤ z w := by sorry
