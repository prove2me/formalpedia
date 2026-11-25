-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_eq_triangular
-- name    : GroundTheory.Automorphic.HarishChandra.canon_eq_triangular
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:08:14.30153+00:00
-- url     : https://prove2.me/theorems/b8d734e0-ec0e-49d5-9695-0d9f08705f15
-- title:
--   Harish Chandra: canon eq triangular
-- statement:
--   The Harish Chandra construction uses the canon eq triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L186-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L186-L189

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

theorem GroundTheory.Automorphic.HarishChandra.canon_eq_triangular (m : Fin n × Fin n →₀ ℕ) :
    canon m = word (blockW (lowL n) m) * hcEmb (monomial (diagExp m) 1) *
      word (blockW (upL n) m) := by sorry
