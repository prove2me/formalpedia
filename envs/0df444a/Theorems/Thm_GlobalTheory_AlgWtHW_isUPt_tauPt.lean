-- Prove2me | Theorems.Thm_GlobalTheory_AlgWtHW_isUPt_tauPt
-- name    : GlobalTheory.AlgWtHW.isUPt_tauPt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:56:53.348823+00:00
-- url     : https://prove2.me/theorems/9fc1b162-f81b-40d5-a756-2db605968a58
-- title:
--   Alg Wt HW: is UPt tau Pt
-- statement:
--   The Alg Wt HW construction uses the is UPt tau Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConjugateNeSelf.lean#L56-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConjugateNeSelf.lean#L56-L70

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

theorem GlobalTheory.AlgWtHW.isUPt_tauPt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : IsUPt (tauPt τ B) := by sorry
