-- Prove2me | Theorems.Thm_GlobalTheory_NormEq_Cmpl_eq_zero_of_forall_mem_piPow
-- name    : GlobalTheory.NormEq.Cmpl.eq_zero_of_forall_mem_piPow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:34:32.227025+00:00
-- url     : https://prove2.me/theorems/e258b5ad-b648-4bde-a1e5-8e77c80da5d5
-- title:
--   Cmpl: eq zero of forall mem pi Pow
-- statement:
--   The Cmpl construction uses the eq zero of forall mem pi Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormFiltrationComplete.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormFiltrationComplete.lean#L92-L98

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

theorem GlobalTheory.NormEq.Cmpl.eq_zero_of_forall_mem_piPow {z : GlobalTheory.UTr.Alg P} (hz : ∀ N, z ∈ piPow h P N) : z = 0 := by sorry
