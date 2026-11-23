-- Prove2me | Theorems.Thm_GlobalTheory_JR_TransferFactor_Cm_act
-- name    : GlobalTheory.JR.TransferFactor.Cm_act
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:14.060835+00:00
-- url     : https://prove2.me/theorems/637286d1-2548-4f17-bf0a-8bc54de62786
-- title:
--   Transfer Factor: Cm act
-- statement:
--   The Transfer Factor construction uses the Cm act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisTransferFactorKrylovDet.lean#L74-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisTransferFactorKrylovDet.lean#L74-L81

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.TransferFactor
variable {k : Type} [CommRing k] {r : ℕ}

theorem GlobalTheory.JR.TransferFactor.Cm_act (g : GL (Fin r) k) (Y : Gl r k) :
    Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by sorry
