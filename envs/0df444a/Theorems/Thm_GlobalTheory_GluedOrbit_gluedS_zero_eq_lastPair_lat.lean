-- Prove2me | Theorems.Thm_GlobalTheory_GluedOrbit_gluedS_zero_eq_lastPair_lat
-- name    : GlobalTheory.GluedOrbit.gluedS_zero_eq_lastPair_lat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:16.491901+00:00
-- url     : https://prove2.me/theorems/83cbc22b-f4a1-4233-92ad-3866df171e9b
-- title:
--   Glued Orbit: glued S zero eq last Pair lat
-- statement:
--   The Glued Orbit construction uses the glued S zero eq last Pair lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SmulGluedLatticeFirstPositionCases.lean#L52-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SmulGluedLatticeFirstPositionCases.lean#L52-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiesOnRamOfInvariant
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmulGluedLatticeFirstPositionCases
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)
noncomputable section
open GlobalTheory GlobalTheory.GluedOrbit
open GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration (interX)
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}

theorem GlobalTheory.GluedOrbit.gluedS_zero_eq_lastPair_lat (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    gluedS q 1 L 0 = (lastPair q L).lat := by sorry
