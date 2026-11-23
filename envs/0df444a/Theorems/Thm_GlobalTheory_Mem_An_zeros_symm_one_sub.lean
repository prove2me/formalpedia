-- Prove2me | Theorems.Thm_GlobalTheory_Mem_An_zeros_symm_one_sub
-- name    : GlobalTheory.Mem.An.zeros_symm_one_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:07.984793+00:00
-- url     : https://prove2.me/theorems/18763b33-af84-4f01-b39c-7fa4d6dfa6a2
-- title:
--   An: zeros symm one sub
-- statement:
--   The An construction uses the zeros symm one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DirichletLZeroSymmetry.lean#L79-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DirichletLZeroSymmetry.lean#L79-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DirichletLZeroSymmetry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex GlobalTheory.Mem.An
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An

theorem GlobalTheory.Mem.An.zeros_symm_one_sub : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      ((DirichletCharacter.LFunction χ ρ = 0 ↔ DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0) ∧
        zmult χ ρ = zmult χ⁻¹ (1 - ρ)) := by sorry
