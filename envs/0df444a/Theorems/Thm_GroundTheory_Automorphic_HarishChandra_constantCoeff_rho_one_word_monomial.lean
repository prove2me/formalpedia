-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_constantCoeff_rho_one_word_monomial
-- name    : GroundTheory.Automorphic.HarishChandra.constantCoeff_rho_one_word_monomial
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:32.418097+00:00
-- url     : https://prove2.me/theorems/1d0e0364-7fdd-4d38-baaf-49f57897efff
-- title:
--   Harish Chandra: constant Coeff rho one word monomial
-- statement:
--   The Harish Chandra construction uses the constant Coeff rho one word monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L346-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L346-L364

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

theorem GroundTheory.Automorphic.HarishChandra.constantCoeff_rho_one_word_monomial (w : List (Fin n × Fin n))
    (s : Fin n × Fin n →₀ ℕ) (h : w.length = s.degree) :
    constantCoeff (rho 1 (word w) (monomial s 1)) ≠ 0 ↔
      Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset _) = s := by sorry
