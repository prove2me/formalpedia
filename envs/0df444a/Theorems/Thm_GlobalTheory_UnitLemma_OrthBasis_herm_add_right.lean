-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_OrthBasis_herm_add_right
-- name    : GlobalTheory.UnitLemma.OrthBasis.herm_add_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:45.444815+00:00
-- url     : https://prove2.me/theorems/352a48d1-a196-435f-a752-73604eb8e960
-- title:
--   Orth Basis: herm add right
-- statement:
--   The Orth Basis construction uses the herm add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermBasisOrthonormal.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermBasisOrthonormal.lean#L14-L16

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

theorem GlobalTheory.UnitLemma.OrthBasis.herm_add_right (x y z₁ z₂ : B.A) : B.herm x y (z₁ + z₂) = B.herm x y z₁ + B.herm x y z₂ := by sorry
