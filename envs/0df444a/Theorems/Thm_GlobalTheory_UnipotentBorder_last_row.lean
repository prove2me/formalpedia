-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentBorder_last_row
-- name    : GlobalTheory.UnipotentBorder.last_row
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:53.264075+00:00
-- url     : https://prove2.me/theorems/0f3251e1-c8e6-46fb-b353-ca73438b358c
-- title:
--   Unipotent Border: last row
-- statement:
--   The Unipotent Border construction uses the last row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L20-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]

theorem GlobalTheory.UnipotentBorder.last_row {n : ℕ} {U L : Matrix (Fin (n+1)) (Fin (n+1)) O} (hU : IsUU U)
    (D : Fin (n+1) → Oˣ) (j : Fin (n+1)) :
    (U * diagonal (fun k => (D k : O)) * L) (Fin.last n) j
      = (D (Fin.last n) : O) * L (Fin.last n) j := by sorry
