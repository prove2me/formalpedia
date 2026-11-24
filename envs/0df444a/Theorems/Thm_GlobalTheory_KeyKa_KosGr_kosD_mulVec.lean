-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_KosGr_kosD_mulVec
-- name    : GlobalTheory.KeyKa.KosGr.kosD_mulVec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:47:23.310815+00:00
-- url     : https://prove2.me/theorems/3c4befda-7b06-4c1b-883f-6a5096b5d9b1
-- title:
--   Kos Gr: kos D mul Vec
-- statement:
--   The Kos Gr construction uses the kos D mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KoszulExactOfGradedRegular.lean#L252-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KoszulExactOfGradedRegular.lean#L252-L286

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosGr

theorem GlobalTheory.KeyKa.KosGr.kosD_mulVec {K : Type} [CommRing K] {g : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K) (w : KIx g 0 N → K)
    (c : Finset (Fin g) → ∀ j, Fin (N j) → K) (h : ∀ I a, w (.inl ⟨I, a⟩) = c I I.card a)
    (I : Finset (Fin g)) (a : Fin (N I.card)) :
    (kosD m (fun _ => 0)).mulVec w (.inl ⟨I, a⟩)
      = dd (V := fun j => Fin (N j) → K) (fun i j => (m i j (j + 1)).mulVecLin) g c I I.card a := by sorry
