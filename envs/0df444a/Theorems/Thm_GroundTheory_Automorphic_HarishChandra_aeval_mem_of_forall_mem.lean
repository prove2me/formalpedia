-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_aeval_mem_of_forall_mem
-- name    : GroundTheory.Automorphic.HarishChandra.aeval_mem_of_forall_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:42.559968+00:00
-- url     : https://prove2.me/theorems/254b8dc0-e1e5-4dfe-88a4-9aa58f9c5813
-- title:
--   Harish Chandra: aeval mem of forall mem
-- statement:
--   The Harish Chandra construction uses the aeval mem of forall mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L37-L43

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

theorem GroundTheory.Automorphic.HarishChandra.aeval_mem_of_forall_mem {A : Subalgebra ℂ (MvPolynomial (Fin n) ℂ)}
    (f : Fin n → MvPolynomial (Fin n) ℂ) (hf : ∀ i, f i ∈ A) (F : MvPolynomial (Fin n) ℂ) :
    aeval f F ∈ A := by sorry
