-- Prove2me | Theorems.Thm_GlobalTheory_LatticeIndicator_finite_quotient_smul_top
-- name    : GlobalTheory.LatticeIndicator.finite_quotient_smul_top
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:00:13.08851+00:00
-- url     : https://prove2.me/theorems/cb99beac-3cd3-430b-8d52-20d75493b8db
-- title:
--   Lattice Indicator: finite quotient smul top
-- statement:
--   The Lattice Indicator construction uses the finite quotient smul top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L200-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L200-L210

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open GlobalTheory.LatticeIndicator

theorem GlobalTheory.LatticeIndicator.finite_quotient_smul_top {O m : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Finite m] {c : O}
    (hc : c ≠ 0) : Finite ((m → O) ⧸ (Ideal.span {c} • (⊤ : Submodule O (m → O)))) := by sorry
