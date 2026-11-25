-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_eq_of_isConjRoot
-- name    : GroundTheory.PAdicHodge.norm_eq_of_isConjRoot
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:38.848998+00:00
-- url     : https://prove2.me/theorems/a6df9331-b3f0-47c6-8558-5422909b5830
-- title:
--   PAdic Hodge: norm eq of is Conj Root
-- statement:
--   The PAdic Hodge construction uses the norm eq of is Conj Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L17-L27

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
variable {F E : Type*} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [NormedField E] [NormedAlgebra F E]

theorem GroundTheory.PAdicHodge.norm_eq_of_isConjRoot {x x' : E} (hx : IsIntegral F x) (h : IsConjRoot F x x') :
    ‖x‖ = ‖x'‖ := by sorry
