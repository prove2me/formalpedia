-- Prove2me | Theorems.Thm_GlobalTheory_IntersectionSymm_not_dim_quotient_le_zero
-- name    : GlobalTheory.IntersectionSymm.not_dim_quotient_le_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:47.254351+00:00
-- url     : https://prove2.me/theorems/dac5caaa-faba-48b5-a437-69e84496e747
-- title:
--   Intersection Symm: not dim quotient le zero
-- statement:
--   The Intersection Symm construction uses the not dim quotient le zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthSumHeightOneDisjointDivisors.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthSumHeightOneDisjointDivisors.lean#L46-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthKerCokerLsmulQuotientSpanSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthSumHeightOneDisjointDivisors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.IntersectionSymm

theorem GlobalTheory.IntersectionSymm.not_dim_quotient_le_zero {A : Type} [CommRing A] (p : Ideal A) [p.IsPrime]
    (hne : ¬ p.IsMaximal) : ¬ ringKrullDim (A ⧸ p) ≤ 0 := by sorry
