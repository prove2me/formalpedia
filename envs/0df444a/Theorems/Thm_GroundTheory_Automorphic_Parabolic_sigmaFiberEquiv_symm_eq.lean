-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_sigmaFiberEquiv_symm_eq
-- name    : GroundTheory.Automorphic.Parabolic.sigmaFiberEquiv_symm_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:31:06.754873+00:00
-- url     : https://prove2.me/theorems/e5b9e982-ddef-5996-b4db-f4c70b683ff0
-- title:
--   Parabolic: sigma Fiber Equiv symm eq
-- statement:
--   The Parabolic construction uses the sigma Fiber Equiv symm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LeviCartan.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LeviCartan.lean#L57-L60

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel
variable {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable (R : Type*) [CommRing R]
variable {β R}

theorem GroundTheory.Automorphic.Parabolic.sigmaFiberEquiv_symm_eq {i : Fin n} {a : Set.range β} (hi : blockOf β i = a) :
    (Equiv.sigmaFiberEquiv (blockOf β)).symm i = ⟨a, ⟨i, hi⟩⟩ := by sorry
