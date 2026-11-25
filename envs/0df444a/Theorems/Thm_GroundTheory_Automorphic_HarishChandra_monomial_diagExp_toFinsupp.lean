-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_monomial_diagExp_toFinsupp
-- name    : GroundTheory.Automorphic.HarishChandra.monomial_diagExp_toFinsupp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:33.536955+00:00
-- url     : https://prove2.me/theorems/8949221b-2dff-4d26-bbc6-7c655002c680
-- title:
--   Harish Chandra: monomial diag Exp to Finsupp
-- statement:
--   The Harish Chandra construction uses the monomial diag Exp to Finsupp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L66-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L66-L80

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
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

theorem GroundTheory.Automorphic.HarishChandra.monomial_diagExp_toFinsupp (w : List (Fin n × Fin n)) (hw : ∀ a ∈ w, a.1 = a.2) :
    monomial (diagExp (Multiset.toFinsupp (w : Multiset (Fin n × Fin n)))) (1 : ℂ) =
      (w.map fun a => X a.1).prod := by sorry
