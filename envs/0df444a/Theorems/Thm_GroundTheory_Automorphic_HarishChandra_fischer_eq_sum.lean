-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_eq_sum
-- name    : GroundTheory.Automorphic.HarishChandra.fischer_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:42.106081+00:00
-- url     : https://prove2.me/theorems/02348ee0-78c6-420f-ace0-050ff9ce3155
-- title:
--   Harish Chandra: fischer eq sum
-- statement:
--   The Harish Chandra construction uses the fischer eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L32-L34

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
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
variable {σ : Type*}

theorem GroundTheory.Automorphic.HarishChandra.fischer_eq_sum (f g : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (hg : g.support ⊆ s) :
    fischer f g = ∑ m ∈ s, (mfact m : ℂ) * star (coeff m f) * coeff m g := by sorry
