-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_KosKer_mulVec_inr
-- name    : GlobalTheory.KeyKa.KosKer.mulVec_inr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:54:43.943498+00:00
-- url     : https://prove2.me/theorems/a2c62900-cf89-4092-bef4-cba0c49f2e62
-- title:
--   Kos Ker: mul Vec inr
-- statement:
--   The Kos Ker construction uses the mul Vec inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MulVecCongrDeg.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MulVecCongrDeg.lean#L53-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MulVecCongrDeg
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
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosKer
open Matrix
variable {g d : ℕ} {N : ℕ → ℕ}

theorem GlobalTheory.KeyKa.KosKer.mulVec_inr {R : Type} [CommRing R] (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (u : KIx g d N → R) (a : Fin d) :
    (kosD m ev *ᵥ u) (.inr a) = (ev 0 *ᵥ (fun k => u (.inl ⟨∅, k⟩))) a := by sorry
