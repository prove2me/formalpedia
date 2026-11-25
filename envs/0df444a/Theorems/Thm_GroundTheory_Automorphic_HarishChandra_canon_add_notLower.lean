-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_add_notLower
-- name    : GroundTheory.Automorphic.HarishChandra.canon_add_notLower
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:09:14.925109+00:00
-- url     : https://prove2.me/theorems/b0e4983c-6bf3-49bb-862e-289524bc1282
-- title:
--   Harish Chandra: canon add not Lower
-- statement:
--   The Harish Chandra construction uses the canon add not Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L273-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L273-L290

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
open scoped IsMulCommutative

theorem GroundTheory.Automorphic.HarishChandra.canon_add_notLower {m m' : Fin n × Fin n →₀ ℕ} (hm' : ∀ a ∈ m'.support, IsLower a) :
    canon m' * word (blockW (diagL n) m) * word (blockW (upL n) m) = canon (m' + notLower m) := by sorry
