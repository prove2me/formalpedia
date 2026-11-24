-- Prove2me | Theorems.Thm_GlobalTheory_CompleteBaseChange_exists_polynomial_sub_mem
-- name    : GlobalTheory.CompleteBaseChange.exists_polynomial_sub_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:11.081703+00:00
-- url     : https://prove2.me/theorems/09c86896-05eb-4073-a953-1ae21199bda0
-- title:
--   Complete Base Change: exists polynomial sub mem
-- statement:
--   The Complete Base Change construction uses the exists polynomial sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsPolynomialSubMem.lean#L84-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsPolynomialSubMem.lean#L84-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsPolynomialSubMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompleteBaseChange

theorem GlobalTheory.CompleteBaseChange.exists_polynomial_sub_mem {O σ τ : Type*} [CommRing O] [Finite σ] [Fintype τ]
    {J : Ideal O} (hJ : J.FG) [IsAdicComplete J O] (f : τ → MvPowerSeries σ O) (N : ℕ)
    (hN : ∀ α : σ →₀ ℕ, α.degree = N → (monomial α (1 : O) : MvPowerSeries σ O) ∈
      Ideal.span (Set.range f) ⊔ J.map (C : O →+* MvPowerSeries σ O))
    (g : MvPowerSeries σ O) :
    ∃ p : MvPolynomial σ O, g - p ∈ Ideal.span (Set.range f) := by sorry
