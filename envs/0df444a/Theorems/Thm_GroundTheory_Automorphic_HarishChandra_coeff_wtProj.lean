-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_coeff_wtProj
-- name    : GroundTheory.Automorphic.HarishChandra.coeff_wtProj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:55.271081+00:00
-- url     : https://prove2.me/theorems/9ae6bf99-d83f-44ae-a841-0a71569aa521
-- title:
--   Harish Chandra: coeff wt Proj
-- statement:
--   The Harish Chandra construction uses the coeff wt Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L116-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L116-L124

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

theorem GroundTheory.Automorphic.HarishChandra.coeff_wtProj (μ : Fin n → ℕ) (m : Fin n × Fin n →₀ ℕ) (f : Poly n) :
    coeff m (wtProj μ f) = if rowWt m = μ then coeff m f else 0 := by sorry
