-- Prove2me | Theorems.Thm_GlobalTheory_AlgWtHW_evPt_eq_upt
-- name    : GlobalTheory.AlgWtHW.evPt_eq_upt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:56:32.987138+00:00
-- url     : https://prove2.me/theorems/4eee1b8d-e0db-443b-9751-6c2ddf7a8409
-- title:
--   Alg Wt HW: ev Pt eq upt
-- statement:
--   The Alg Wt HW construction uses the ev Pt eq upt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConjugateNeSelf.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConjugateNeSelf.lean#L51-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix
open GlobalTheory GlobalTheory.AlgWtHW
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem GlobalTheory.AlgWtHW.evPt_eq_upt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : evPt τ B = upt (tauPt τ B) := by sorry
