-- Prove2me | Theorems.Thm_GlobalTheory_AlgWtHW_conj_conj
-- name    : GlobalTheory.AlgWtHW.conj_conj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:56:29.133799+00:00
-- url     : https://prove2.me/theorems/70cc672a-6baf-4f6e-80c1-78b0ea8c76bb
-- title:
--   Alg Wt HW: conj conj
-- statement:
--   The Alg Wt HW construction uses the conj conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConjugateNeSelf.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConjugateNeSelf.lean#L29-L31

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

theorem GlobalTheory.AlgWtHW.conj_conj (φ : L →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by sorry
