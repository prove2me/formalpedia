-- Prove2me | Theorems.Thm_GlobalTheory_freeAlgebra_compHom_isScalarTower
-- name    : GlobalTheory.freeAlgebra_compHom_isScalarTower
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:54:14.129828+00:00
-- url     : https://prove2.me/theorems/326ca4e7-9741-48d5-a960-a84e07709235
-- title:
--   Global Theory: free Algebra comp Hom is Scalar Tower
-- statement:
--   The Global Theory construction uses the free Algebra comp Hom is Scalar Tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EndomorphismFamilyDirectSummandCancellation.lean#L6-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EndomorphismFamilyDirectSummandCancellation.lean#L6-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelArtinianNoetherianSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismFamilyDirectSummandCancellation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.freeAlgebra_compHom_isScalarTower {k ι W : Type} [Field k] [AddCommGroup W] [Module k W]
    (φ : FreeAlgebra k ι →ₐ[k] Module.End k W) :
    @IsScalarTower k (FreeAlgebra k ι) W _ (Module.compHom W φ.toRingHom).toSMul _ := by sorry
