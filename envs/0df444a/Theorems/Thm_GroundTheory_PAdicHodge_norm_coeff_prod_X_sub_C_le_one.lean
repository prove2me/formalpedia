-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_coeff_prod_X_sub_C_le_one
-- name    : GroundTheory.PAdicHodge.norm_coeff_prod_X_sub_C_le_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:29.444616+00:00
-- url     : https://prove2.me/theorems/eaf3ba80-0e40-4ea0-93c7-74c2e48fda23
-- title:
--   PAdic Hodge: norm coeff prod X sub C le one
-- statement:
--   The PAdic Hodge construction uses the norm coeff prod X sub C le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L91-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L91-L99

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {E : Type*} [NormedField E] [IsUltrametricDist E]

theorem GroundTheory.PAdicHodge.norm_coeff_prod_X_sub_C_le_one {s : Multiset E} (hs : ∀ r ∈ s, ‖r‖ ≤ 1) (k : ℕ) :
    ‖((s.map fun r => X - C r).prod).coeff k‖ ≤ 1 := by sorry
