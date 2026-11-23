-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_finite_inter_singularSet
-- name    : GroundTheory.Global.Elliptic.finite_inter_singularSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:07.098805+00:00
-- url     : https://prove2.me/theorems/bbf1a121-ca8c-4369-b3ed-62575bfd7b3a
-- title:
--   Elliptic: finite inter singular Set
-- statement:
--   The Elliptic construction uses the finite inter singular Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticFunctions.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticFunctions.lean#L114-L119

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable (L : PeriodPair)
variable {L}
variable (L)
variable {L}

theorem GroundTheory.Global.Elliptic.finite_inter_singularSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f) {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ singularSet f).Finite := by sorry
