-- Prove2me | Theorems.Thm_GlobalTheory_JR_OrbitProper_cont_Bm
-- name    : GlobalTheory.JR.OrbitProper.cont_Bm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:35:06.866892+00:00
-- url     : https://prove2.me/theorems/bd5796c0-5eff-453b-a370-ff57832d2aac
-- title:
--   Orbit Proper: cont Bm
-- statement:
--   The Orbit Proper construction uses the cont Bm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L117-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L117-L122

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

theorem GlobalTheory.JR.OrbitProper.cont_Bm : Continuous (fun Y : Gl r F => Bm Y) := by sorry
