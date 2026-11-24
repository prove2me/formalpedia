-- Prove2me | Theorems.Thm_GlobalTheory_NormEq_Cmpl_exists_lim_alg
-- name    : GlobalTheory.NormEq.Cmpl.exists_lim_alg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:34:36.648897+00:00
-- url     : https://prove2.me/theorems/4d38f908-8ed8-4e6c-9a9c-cdbea4eeaf86
-- title:
--   Cmpl: exists lim alg
-- statement:
--   The Cmpl construction uses the exists lim alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormFiltrationComplete.lean#L100-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormFiltrationComplete.lean#L100-L120

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
variable {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (sigO σ h.2.1))

theorem GlobalTheory.NormEq.Cmpl.exists_lim_alg [CompleteSpace L] (a : ℕ → GlobalTheory.UTr.Alg P)
    (ha : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, a n - a m ∈ piPow h P N) :
    ∃ y, ∀ N, ∀ᶠ n in atTop, a n - y ∈ piPow h P N := by sorry
