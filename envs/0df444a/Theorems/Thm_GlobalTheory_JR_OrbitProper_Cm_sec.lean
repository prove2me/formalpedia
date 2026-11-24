-- Prove2me | Theorems.Thm_GlobalTheory_JR_OrbitProper_Cm_sec
-- name    : GlobalTheory.JR.OrbitProper.Cm_sec
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:35:43.06515+00:00
-- url     : https://prove2.me/theorems/0ea785b8-4e54-4e9e-9965-59505ce9fefd
-- title:
--   Orbit Proper: Cm sec
-- statement:
--   The Orbit Proper construction uses the Cm sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L48-L52

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
variable {r : ℕ} {k : Type} [CommRing k]

theorem GlobalTheory.JR.OrbitProper.Cm_sec (a : Inv r k) : Cm (sec a) = hankel a := by sorry
