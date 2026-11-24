-- Prove2me | Theorems.Thm_GlobalTheory_PolModLattice_exists_inv
-- name    : GlobalTheory.PolModLattice.exists_inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:50:19.982632+00:00
-- url     : https://prove2.me/theorems/d668de97-f657-470a-8d1d-47a01858f335
-- title:
--   Pol Mod Lattice: exists inv
-- statement:
--   The Pol Mod Lattice construction uses the exists inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarizationModuleUnitDual.lean#L155-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarizationModuleUnitDual.lean#L155-L253

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
open GlobalTheory GlobalTheory.PolModLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open scoped nonZeroDivisors

theorem GlobalTheory.PolModLattice.exists_inv (L : Submodule (OF E) E)
    (hL : ∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) :
    ∃ J : Submodule (OF E) E, formSpan L * J = 1 ∧ ∀ j ∈ J, bar j = -j := by sorry
