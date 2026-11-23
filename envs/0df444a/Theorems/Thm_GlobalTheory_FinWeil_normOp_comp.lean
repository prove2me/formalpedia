-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_normOp_comp
-- name    : GlobalTheory.FinWeil.normOp_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:54.448521+00:00
-- url     : https://prove2.me/theorems/e58ea5a6-8329-4378-9360-2010c3a67680
-- title:
--   Fin Weil: norm Op comp
-- statement:
--   The Fin Weil construction uses the norm Op comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/NormalizedHeisenbergIntertwinerComp.lean#L14-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/NormalizedHeisenbergIntertwinerComp.lean#L14-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedIntertwinerCompOfAdjacentLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumCompOfIntermediateLattiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_AdjacentSelfDualLatticesIndexSimpleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsAdjacentSelfDualLatticeTowardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil

theorem GlobalTheory.FinWeil.normOp_comp : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by sorry
