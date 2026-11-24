-- Prove2me | Theorems.Thm_GlobalTheory_NormEq_isUnit_of_sub_one_mem
-- name    : GlobalTheory.NormEq.isUnit_of_sub_one_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:52.444781+00:00
-- url     : https://prove2.me/theorems/9d9795c1-17d9-4b3c-b789-2be41f90bebe
-- title:
--   Norm Eq: is Unit of sub one mem
-- statement:
--   The Norm Eq construction uses the is Unit of sub one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUnitOneAddPiOMul.lean#L118-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUnitOneAddPiOMul.lean#L118-L126

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

theorem GlobalTheory.NormEq.isUnit_of_sub_one_mem {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) {m : ℕ} (hm : 1 ≤ m) {x : GlobalTheory.UTr.Alg P} (hx : x - 1 ∈ piPow h P m) :
    IsUnit x := by sorry
