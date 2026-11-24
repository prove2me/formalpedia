-- Prove2me | Theorems.Thm_GlobalTheory_JR_OrbitProper_contAt_hankel_inv
-- name    : GlobalTheory.JR.OrbitProper.contAt_hankel_inv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:34:33.334314+00:00
-- url     : https://prove2.me/theorems/f2d7e1fc-0e1b-4822-8110-54a2462c74ac
-- title:
--   Orbit Proper: cont At hankel inv
-- statement:
--   The Orbit Proper construction uses the cont At hankel inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L131-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L131-L135

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbitProper
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem GlobalTheory.JR.OrbitProper.contAt_hankel_inv (a : Inv r F) (ha : Delta a ≠ 0) :
    ContinuousAt (fun b : Inv r F => (hankel b)⁻¹) a := by sorry
