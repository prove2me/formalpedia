-- Prove2me | Theorems.Thm_GlobalTheory_JR_OrbitProper_coe_eq
-- name    : GlobalTheory.JR.OrbitProper.coe_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:35:43.486304+00:00
-- url     : https://prove2.me/theorems/351da935-2ae3-44e4-afbd-53389bd90dc7
-- title:
--   Orbit Proper: coe eq
-- statement:
--   The Orbit Proper construction uses the coe eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L137-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L137-L139

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

theorem GlobalTheory.JR.OrbitProper.coe_eq (g : GL (Fin r) F) (a : Inv r F) :
    (g : Matrix (Fin r) (Fin r) F) = Bm (act g (sec a)) := by sorry
