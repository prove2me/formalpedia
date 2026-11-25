-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mfact_add_single
-- name    : GroundTheory.Automorphic.HarishChandra.mfact_add_single
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:15.021083+00:00
-- url     : https://prove2.me/theorems/c8de8291-a91f-421f-b137-9617a6b607a7
-- title:
--   Harish Chandra: mfact add single
-- statement:
--   The Harish Chandra construction uses the mfact add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/FischerForm.lean#L14-L27

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

theorem GroundTheory.Automorphic.HarishChandra.mfact_add_single [DecidableEq σ] (s : σ →₀ ℕ) (a : σ) :
    mfact (s + Finsupp.single a 1) = mfact s * (s a + 1) := by sorry
