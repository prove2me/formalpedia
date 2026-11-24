-- Prove2me | Theorems.Thm_GlobalTheory_JR_OrbitProper_cont_charpoly_coeff
-- name    : GlobalTheory.JR.OrbitProper.cont_charpoly_coeff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:34:46.765005+00:00
-- url     : https://prove2.me/theorems/2b5698f9-86a5-4323-affe-97bfcae5eabe
-- title:
--   Orbit Proper: cont charpoly coeff
-- statement:
--   The Orbit Proper construction uses the cont charpoly coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L82-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L82-L92

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

theorem GlobalTheory.JR.OrbitProper.cont_charpoly_coeff (i : ℕ) :
    Continuous (fun A : Matrix (Fin r) (Fin r) F => A.charpoly.coeff i) := by sorry
