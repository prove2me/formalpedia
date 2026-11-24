-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_eq_of_isPrimitiveRoot_of_isUltrametricDist
-- name    : GroundTheory.PAdicHodge.norm_sub_one_eq_of_isPrimitiveRoot_of_isUltrametricDist
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:17.739978+00:00
-- url     : https://prove2.me/theorems/76011634-327c-49f0-8ce9-f5fbc9978376
-- title:
--   PAdic Hodge: norm sub one eq of is Primitive Root of is Ultrametric Dist
-- statement:
--   The PAdic Hodge construction uses the norm sub one eq of is Primitive Root of is Ultrametric Dist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L31-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L31-L41

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
variable {F : Type*} [NormedField F] [IsUltrametricDist F]

theorem GroundTheory.PAdicHodge.norm_sub_one_eq_of_isPrimitiveRoot_of_isUltrametricDist {ζ μ : F} {k : ℕ} [NeZero k]
    (hζ : IsPrimitiveRoot ζ k) (hμ : IsPrimitiveRoot μ k) : ‖μ - 1‖ = ‖ζ - 1‖ := by sorry
