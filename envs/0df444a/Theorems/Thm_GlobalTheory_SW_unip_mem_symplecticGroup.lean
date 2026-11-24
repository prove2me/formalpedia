-- Prove2me | Theorems.Thm_GlobalTheory_SW_unip_mem_symplecticGroup
-- name    : GlobalTheory.SW.unip_mem_symplecticGroup
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:20.318468+00:00
-- url     : https://prove2.me/theorems/127a7761-495d-40b9-b141-d56a0846be20
-- title:
--   SW: unip mem symplectic Group
-- statement:
--   The SW construction uses the unip mem symplectic Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SymplecticEqParabolicJParabolicJParabolic.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SymplecticEqParabolicJParabolicJParabolic.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticEqParabolicJParabolicJParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open private exists_symmetric_X_isUnit_det_add_mul_of_symplectic from Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory GlobalTheory.SW

theorem GlobalTheory.SW.unip_mem_symplecticGroup {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℚ}
    (hX : X.IsSymm) : (fromBlocks 1 X 0 1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) ∈ symplecticGroup ι ℚ := by sorry
