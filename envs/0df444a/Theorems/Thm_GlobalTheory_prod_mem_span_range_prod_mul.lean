-- Prove2me | Theorems.Thm_GlobalTheory_prod_mem_span_range_prod_mul
-- name    : GlobalTheory.prod_mem_span_range_prod_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:11.375854+00:00
-- url     : https://prove2.me/theorems/c11eff2d-a5fa-4a46-82a3-dad6500d68c9
-- title:
--   Global Theory: prod mem span range prod mul
-- statement:
--   The Global Theory construction uses the prod mem span range prod mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ManyIndependentProductsInFunctionField.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ManyIndependentProductsInFunctionField.lean#L11-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinRootMapComplexLinearIndependentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormalBranchesOfSeparableReductionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveMonicSeparableSpecializationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ManyIndependentProductsInFunctionField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.prod_mem_span_range_prod_mul {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type*} [Fintype J] (g : J → A) (m : ℕ) (f : Fin m → A)
    (hf : ∀ l, f l ∈ Submodule.span R (Set.range g)) (y : A) :
    (∏ l, f l) * y ∈
      Submodule.span R (Set.range fun u : Fin m → J => (∏ l, g (u l)) * y) := by sorry
