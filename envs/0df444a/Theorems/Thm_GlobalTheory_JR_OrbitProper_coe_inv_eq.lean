-- Prove2me | Theorems.Thm_GlobalTheory_JR_OrbitProper_coe_inv_eq
-- name    : GlobalTheory.JR.OrbitProper.coe_inv_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:35:12.638563+00:00
-- url     : https://prove2.me/theorems/bb354f1e-a57f-4607-ad17-4ef7524d6ca9
-- title:
--   Orbit Proper: coe inv eq
-- statement:
--   The Orbit Proper construction uses the coe inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L141-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L141-L144

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

theorem GlobalTheory.JR.OrbitProper.coe_inv_eq (g : GL (Fin r) F) (a : Inv r F) (ha : Delta a ≠ 0) :
    ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = (hankel a)⁻¹ * Cm (act g (sec a)) := by sorry
