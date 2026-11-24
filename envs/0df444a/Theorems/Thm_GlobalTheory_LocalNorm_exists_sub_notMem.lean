-- Prove2me | Theorems.Thm_GlobalTheory_LocalNorm_exists_sub_notMem
-- name    : GlobalTheory.LocalNorm.exists_sub_notMem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:13:47.650082+00:00
-- url     : https://prove2.me/theorems/a24f16c2-f197-400d-a48c-20f1f6127e32
-- title:
--   Local Norm: exists sub not Mem
-- statement:
--   The Local Norm construction uses the exists sub not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsBinaryEqAdicCompletion.lean#L97-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsBinaryEqAdicCompletion.lean#L97-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LocalNorm

theorem GlobalTheory.LocalNorm.exists_sub_notMem {A B : Type*} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra.Unramified A B] (σ : B →ₐ[A] B) (hσ : ∃ b, σ b ≠ b) (P : Ideal B) (hP : P ≠ ⊤) :
    ∃ b, b - σ b ∉ P := by sorry
