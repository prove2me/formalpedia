-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_wtProj
-- name    : GroundTheory.Automorphic.HarishChandra.fischer_wtProj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:19.998879+00:00
-- url     : https://prove2.me/theorems/0c6948e5-6d0a-4678-8949-6b73e51deeab
-- title:
--   Harish Chandra: fischer wt Proj
-- statement:
--   The Harish Chandra construction uses the fischer wt Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L183-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L183-L195

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.fischer_wtProj (μ : Fin n → ℕ) (f g : Poly n) :
    fischer (wtProj μ f) g = fischer f (wtProj μ g) := by sorry
