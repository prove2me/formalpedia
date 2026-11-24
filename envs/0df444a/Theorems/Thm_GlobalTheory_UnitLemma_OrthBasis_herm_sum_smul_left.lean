-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_OrthBasis_herm_sum_smul_left
-- name    : GlobalTheory.UnitLemma.OrthBasis.herm_sum_smul_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:47.163854+00:00
-- url     : https://prove2.me/theorems/e20144d0-2fd0-40a3-9590-98b5eeaa51cc
-- title:
--   Orth Basis: herm sum smul left
-- statement:
--   The Orth Basis construction uses the herm sum smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermBasisOrthonormal.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermBasisOrthonormal.lean#L26-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermBasisOrthonormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.OrthBasis
open GlobalTheory.UnitLemma
variable {K : UQ} (B : InvAlg K)

theorem GlobalTheory.UnitLemma.OrthBasis.herm_sum_smul_left {n : ℕ} (x z : B.A) (a : Fin n → K.E) (v : Fin n → B.A) :
    B.herm x (∑ j, a j • v j) z = ∑ j, a j * B.herm x (v j) z := by sorry
