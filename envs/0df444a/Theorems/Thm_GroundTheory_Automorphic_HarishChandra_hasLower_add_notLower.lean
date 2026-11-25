-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hasLower_add_notLower
-- name    : GroundTheory.Automorphic.HarishChandra.hasLower_add_notLower
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:09:27.856822+00:00
-- url     : https://prove2.me/theorems/44b75c58-1d43-4d7a-b33d-8f769358ed6b
-- title:
--   Harish Chandra: has Lower add not Lower
-- statement:
--   The Harish Chandra construction uses the has Lower add not Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L300-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L300-L306

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

theorem GroundTheory.Automorphic.HarishChandra.hasLower_add_notLower {m m' : Fin n × Fin n →₀ ℕ} (hm' : ∀ a ∈ m'.support, IsLower a)
    (hdeg : 1 ≤ m'.degree) : HasLower (m' + notLower m) := by sorry
