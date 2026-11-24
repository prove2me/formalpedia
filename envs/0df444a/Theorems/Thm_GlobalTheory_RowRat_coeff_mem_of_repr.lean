-- Prove2me | Theorems.Thm_GlobalTheory_RowRat_coeff_mem_of_repr
-- name    : GlobalTheory.RowRat.coeff_mem_of_repr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:32:58.163684+00:00
-- url     : https://prove2.me/theorems/9969c156-8616-459c-919a-3d2dd0d4d2d3
-- title:
--   Row Rat: coeff mem of repr
-- statement:
--   The Row Rat construction uses the coeff mem of repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ReprMemOfCoeff.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ReprMemOfCoeff.lean#L26-L34

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

theorem GlobalTheory.RowRat.coeff_mem_of_repr {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L]
    (κ : L →+* ℂ) (v : VV ℂ lam) (h : ∀ a, (bVV ℂ lam).repr v a ∈ Set.range κ) (m : ι × Fin n × Fin n →₀ ℕ) :
    coeff m v.1 ∈ Set.range κ := by sorry
