-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowWt_eq_of_eigen
-- name    : GroundTheory.Automorphic.HarishChandra.rowWt_eq_of_eigen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:05.602081+00:00
-- url     : https://prove2.me/theorems/7650d480-9396-45b5-b5fb-08bc0e6927d1
-- title:
--   Harish Chandra: row Wt eq of eigen
-- statement:
--   The Harish Chandra construction uses the row Wt eq of eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L89-L93

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

theorem GroundTheory.Automorphic.HarishChandra.rowWt_eq_of_eigen {h : Poly n} {c : Fin n → ℂ} (hc : ∀ a, rowOp a a h = c a • h)
    {m : Fin n × Fin n →₀ ℕ} (hm : m ∈ h.support) (a : Fin n) : (rowWt m a : ℂ) = c a := by sorry
