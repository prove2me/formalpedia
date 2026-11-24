-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_TopClose_prod
-- name    : GroundTheory.Automorphic.HarishChandra.TopClose.prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:53.212234+00:00
-- url     : https://prove2.me/theorems/2ff6fca6-0d5f-4ef0-8ead-481c0a220812
-- title:
--   Top Close: prod
-- statement:
--   The Top Close construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L93-L101

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Symmetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial Finset
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.TopClose.prod {ι : Type*} (s : Finset ι) (k : ι → ℕ) (a b : ι → MvPolynomial (Fin n) ℂ)
    (h : ∀ i ∈ s, TopClose (k i) (a i) (b i)) :
    TopClose (∑ i ∈ s, k i) (∏ i ∈ s, a i) (∏ i ∈ s, b i) := by sorry
