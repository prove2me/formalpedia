-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_lowL
-- name    : GroundTheory.Automorphic.HarishChandra.mem_lowL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:07:14.895827+00:00
-- url     : https://prove2.me/theorems/495ae4c4-1514-47ef-b590-14fcf5add4d3
-- title:
--   Harish Chandra: mem low L
-- statement:
--   The Harish Chandra construction uses the mem low L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L31-L32

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.mem_lowL {a : Fin n × Fin n} : a ∈ lowL n ↔ IsLower a := by sorry
