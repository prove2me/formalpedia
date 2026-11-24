-- Prove2me | Theorems.Thm_GlobalTheory_JR_TransferFactor_vrow_poly
-- name    : GlobalTheory.JR.TransferFactor.vrow_poly
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:36:59.038328+00:00
-- url     : https://prove2.me/theorems/b3e7dd91-7051-4e09-b809-18e3ff3cc847
-- title:
--   Transfer Factor: vrow poly
-- statement:
--   The Transfer Factor construction uses the vrow poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisTransferFactorKrylovDet.lean#L24-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisTransferFactorKrylovDet.lean#L24-L43

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

theorem GlobalTheory.JR.TransferFactor.vrow_poly (Y : Gl r k) (i : ℕ) : ∃ p : Polynomial k, p.coeff i = 1 ∧ (∀ N, i < N → p.coeff N = 0) ∧
    (fun l => vrow Y (i + 1) (Fin.castSucc l)) = Y.2.2.1 ᵥ* Polynomial.aeval Y.1 p := by sorry
