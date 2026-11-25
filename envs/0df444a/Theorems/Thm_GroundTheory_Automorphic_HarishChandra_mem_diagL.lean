-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_diagL
-- name    : GroundTheory.Automorphic.HarishChandra.mem_diagL
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:07:34.114621+00:00
-- url     : https://prove2.me/theorems/14b15ab3-a397-44bd-9b53-1df9cba5a38b
-- title:
--   Harish Chandra: mem diag L
-- statement:
--   The Harish Chandra construction uses the mem diag L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L34-L35

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

theorem GroundTheory.Automorphic.HarishChandra.mem_diagL {a : Fin n × Fin n} : a ∈ diagL n ↔ IsDiag a := by sorry
