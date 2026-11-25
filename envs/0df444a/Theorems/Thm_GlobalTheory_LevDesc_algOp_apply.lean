-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_algOp_apply
-- name    : GlobalTheory.LevDesc.algOp_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:32.135082+00:00
-- url     : https://prove2.me/theorems/8c8ed2cb-5e39-48e2-adbd-f642d80178fb
-- title:
--   Lev Desc: alg Op apply
-- statement:
--   The Lev Desc construction uses the alg Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L77-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {G K R : Type} [Group G] [Field K] [CommRing R] [Algebra K R]
variable (st : G → R →ₐ[K] R)

theorem GlobalTheory.LevDesc.algOp_apply [Fintype G] (e : MonoidAlgebra K G) (x : R) :
    algOp st e x = ∑ g, e.coeff g • st g⁻¹ x := by sorry
