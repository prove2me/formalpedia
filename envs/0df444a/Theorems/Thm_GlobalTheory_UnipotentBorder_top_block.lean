-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentBorder_top_block
-- name    : GlobalTheory.UnipotentBorder.top_block
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:28.924887+00:00
-- url     : https://prove2.me/theorems/24833a38-e7f3-4d8d-826a-8e03232b4234
-- title:
--   Unipotent Border: top block
-- statement:
--   The Unipotent Border construction uses the top block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L44-L50

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

theorem GlobalTheory.UnipotentBorder.top_block {n : ℕ} (U L : Matrix (Fin (n+1)) (Fin (n+1)) O)
    (D : Fin (n+1) → Oˣ) (i j : Fin n) :
    (U * diagonal (fun k => (D k : O)) * L) i.castSucc j.castSucc =
      (U.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n => (D k.castSucc : O)) *
        L.submatrix Fin.castSucc Fin.castSucc) i j
      + U i.castSucc (Fin.last n) * (D (Fin.last n) : O) * L (Fin.last n) j.castSucc := by sorry
