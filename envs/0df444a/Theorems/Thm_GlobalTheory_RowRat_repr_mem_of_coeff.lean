-- Prove2me | Theorems.Thm_GlobalTheory_RowRat_repr_mem_of_coeff
-- name    : GlobalTheory.RowRat.repr_mem_of_coeff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:33:03.743231+00:00
-- url     : https://prove2.me/theorems/09c29e84-52fe-4a3a-8f05-84994f9efa20
-- title:
--   Row Rat: repr mem of coeff
-- statement:
--   The Row Rat construction uses the repr mem of coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ReprMemOfCoeff.lean#L41-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ReprMemOfCoeff.lean#L41-L68

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ReprMemOfCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.L2.DIV MvPolynomial
open GlobalTheory GlobalTheory.RowRat
open Formalism.L2.DIV MvPolynomial

theorem GlobalTheory.RowRat.repr_mem_of_coeff {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L]
    (κ : L →+* ℂ) (v : VV ℂ lam) (h : ∀ m, coeff m v.1 ∈ Set.range κ) (a : VVIdx lam) :
    (bVV ℂ lam).repr v a ∈ Set.range κ := by sorry
