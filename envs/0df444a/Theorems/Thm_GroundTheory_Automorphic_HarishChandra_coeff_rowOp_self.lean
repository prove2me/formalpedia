-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_coeff_rowOp_self
-- name    : GroundTheory.Automorphic.HarishChandra.coeff_rowOp_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:04.373528+00:00
-- url     : https://prove2.me/theorems/7ef5d90e-bad9-47c2-9e22-9a2e6b150093
-- title:
--   Harish Chandra: coeff row Op self
-- statement:
--   The Harish Chandra construction uses the coeff row Op self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L78-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L78-L87

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

theorem GroundTheory.Automorphic.HarishChandra.coeff_rowOp_self (i : Fin n) (m : Fin n × Fin n →₀ ℕ) (f : Poly n) :
    coeff m (rowOp i i f) = (rowWt m i : ℂ) * coeff m f := by sorry
