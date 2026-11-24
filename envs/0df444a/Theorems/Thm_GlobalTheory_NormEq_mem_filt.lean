-- Prove2me | Theorems.Thm_GlobalTheory_NormEq_mem_filt
-- name    : GlobalTheory.NormEq.mem_filt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:34:16.992608+00:00
-- url     : https://prove2.me/theorems/da17014d-7a73-4109-8fe1-3ce610d37d05
-- title:
--   Norm Eq: mem filt
-- statement:
--   The Norm Eq construction uses the mem filt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUnitOneAddPiOMul.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUnitOneAddPiOMul.lean#L56-L57

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.UG
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.NormEq.mem_filt {ϖ : L} {σ : L →+* L} {q : ℕ} {h : IsUnramInv ϖ σ q} {P : GlobalTheory.UTr.Csr (sigO σ h.2.1)} {m : ℕ}
    {u : (GlobalTheory.UTr.Alg P)ˣ} : u ∈ filt h P m ↔ (u : GlobalTheory.UTr.Alg P) - 1 ∈ piPow h P m := by sorry
