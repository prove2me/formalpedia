-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_OrthBasis_herm_zero_right
-- name    : GlobalTheory.UnitLemma.OrthBasis.herm_zero_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:52.832602+00:00
-- url     : https://prove2.me/theorems/9ce24f5f-9c64-4f5f-8570-accbdd1b3a12
-- title:
--   Orth Basis: herm zero right
-- statement:
--   The Orth Basis construction uses the herm zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermBasisOrthonormal.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermBasisOrthonormal.lean#L18-L20

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

theorem GlobalTheory.UnitLemma.OrthBasis.herm_zero_right (x y : B.A) : B.herm x y 0 = 0 := by sorry
