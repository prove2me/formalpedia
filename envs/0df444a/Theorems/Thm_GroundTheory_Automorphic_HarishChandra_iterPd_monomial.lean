-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_monomial
-- name    : GroundTheory.Automorphic.HarishChandra.iterPd_monomial
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:14.734367+00:00
-- url     : https://prove2.me/theorems/3674b107-4114-4e8c-8e24-57c09186abc5
-- title:
--   Harish Chandra: iter Pd monomial
-- statement:
--   The Harish Chandra construction uses the iter Pd monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L318-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L318-L344

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
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

theorem GroundTheory.Automorphic.HarishChandra.iterPd_monomial (w : List (Fin n × Fin n)) (s : Fin n × Fin n →₀ ℕ) (c : ℂ) :
    ∃ κ : ℂ, iterPd w (monomial s c) =
        monomial (s - Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset _)) (c * κ) ∧
      (κ ≠ 0 ↔ Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset _) ≤ s) := by sorry
