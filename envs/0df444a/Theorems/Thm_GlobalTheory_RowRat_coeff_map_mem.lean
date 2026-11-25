-- Prove2me | Theorems.Thm_GlobalTheory_RowRat_coeff_map_mem
-- name    : GlobalTheory.RowRat.coeff_map_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:24:43.569115+00:00
-- url     : https://prove2.me/theorems/a01a45aa-4ffd-5cd5-ae87-c803296477b6
-- title:
--   Row Rat: coeff map mem
-- statement:
--   The Row Rat construction uses the coeff map mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ReprMemOfCoeff.lean#L75-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ReprMemOfCoeff.lean#L75-L86

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

theorem GlobalTheory.RowRat.coeff_map_mem {ι : Type} [Fintype ι] {n n' : ℕ} {σ : ι → Formalism.BasicNotions.DomWeight n} {σ' : ι → Formalism.BasicNotions.DomWeight n'} {L : Type} [Field L] (κ : L →+* ℂ)
    (f : VV ℂ σ →ₗ[ℂ] VV ℂ σ') (hf : ∀ a b, (bVV ℂ σ').repr (f (bVV ℂ σ b)) a ∈ Set.range κ) (v : VV ℂ σ)
    (hv : ∀ m, coeff m v.1 ∈ Set.range κ) (m : ι × Fin n' × Fin n' →₀ ℕ) : coeff m (f v).1 ∈ Set.range κ := by sorry
