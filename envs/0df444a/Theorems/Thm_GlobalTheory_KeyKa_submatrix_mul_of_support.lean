-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_submatrix_mul_of_support
-- name    : GlobalTheory.KeyKa.submatrix_mul_of_support
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:49:30.478237+00:00
-- url     : https://prove2.me/theorems/115288b4-e480-4172-8b9c-94cc3f247d6d
-- title:
--   Key Ka: submatrix mul of support
-- statement:
--   The Key Ka construction uses the submatrix mul of support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SubmatrixMulOfSupport.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SubmatrixMulOfSupport.lean#L31-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.submatrix_mul_of_support {R Ix J K L : Type} [CommRing R] [Fintype Ix] [Fintype L]
    (A B : Matrix Ix Ix R) (f : J → Ix) (g : K → Ix) (i : L → Ix) (hi : Function.Injective i)
    (h : ∀ p q r, r ∉ Set.range i → A (f p) r * B r (g q) = 0) :
    (A * B).submatrix f g = A.submatrix f i * B.submatrix i g := by sorry
