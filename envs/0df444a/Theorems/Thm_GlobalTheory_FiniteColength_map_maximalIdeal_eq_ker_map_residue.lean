-- Prove2me | Theorems.Thm_GlobalTheory_FiniteColength_map_maximalIdeal_eq_ker_map_residue
-- name    : GlobalTheory.FiniteColength.map_maximalIdeal_eq_ker_map_residue
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:33:48.236196+00:00
-- url     : https://prove2.me/theorems/b1357f30-6255-4025-8362-4e06f1c33291
-- title:
--   Finite Colength: map maximal Ideal eq ker map residue
-- statement:
--   The Finite Colength construction uses the map maximal Ideal eq ker map residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MapMaximalIdealEqKerMapResidue.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MapMaximalIdealEqKerMapResidue.lean#L11-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsWeaklyRegularMvPowerSeriesOfFiniteColengthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatMvPowerSeriesOfIsNoetherianRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatQuotientWeaklyRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MapMaximalIdealEqKerMapResidue
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.FiniteColength

theorem GlobalTheory.FiniteColength.map_maximalIdeal_eq_ker_map_residue (T : Type) [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T] (σ : Type) :
    (maximalIdeal T).map (algebraMap T (MvPowerSeries σ T)) =
      RingHom.ker (MvPowerSeries.map (σ := σ) (residue T)) := by sorry
