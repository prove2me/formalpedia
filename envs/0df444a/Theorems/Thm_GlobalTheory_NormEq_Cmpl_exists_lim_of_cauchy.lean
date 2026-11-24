-- Prove2me | Theorems.Thm_GlobalTheory_NormEq_Cmpl_exists_lim_of_cauchy
-- name    : GlobalTheory.NormEq.Cmpl.exists_lim_of_cauchy
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:35:13.244356+00:00
-- url     : https://prove2.me/theorems/d0b7b4d6-90ad-466f-87fc-2e6b28147ca3
-- title:
--   Cmpl: exists lim of cauchy
-- statement:
--   The Cmpl construction uses the exists lim of cauchy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormFiltrationComplete.lean#L31-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormFiltrationComplete.lean#L31-L62

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFiltrationComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.NormEq GlobalTheory.NormEq.Cmpl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.NormEq.Cmpl.exists_lim_of_cauchy [CompleteSpace L] {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (s : ℕ → L) (hsO : ∀ n, Valued.v (s n) ≤ 1)
    (hs : ∀ N : ℕ, ∃ M, ∀ m ≥ M, ∀ n ≥ M, Valued.v (s n - s m) ≤ Valued.v ϖ ^ N) :
    ∃ ℓ, Valued.v ℓ ≤ 1 ∧ ∀ N : ℕ, ∀ᶠ n in atTop, Valued.v (s n - ℓ) ≤ Valued.v ϖ ^ N := by sorry
