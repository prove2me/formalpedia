-- Prove2me | Theorems.Thm_GlobalTheory_AlgWtHW_conjugate_ne_self
-- name    : GlobalTheory.AlgWtHW.conjugate_ne_self
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:56:14.885054+00:00
-- url     : https://prove2.me/theorems/09cfb271-94f6-4230-a775-82aae1cbaf7d
-- title:
--   Alg Wt HW: conjugate ne self
-- statement:
--   The Alg Wt HW construction uses the conjugate ne self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConjugateNeSelf.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConjugateNeSelf.lean#L33-L34

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

theorem GlobalTheory.AlgWtHW.conjugate_ne_self (τ : L →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := by sorry
