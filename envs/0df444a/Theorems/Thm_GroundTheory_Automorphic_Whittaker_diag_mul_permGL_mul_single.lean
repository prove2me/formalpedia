-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_diag_mul_permGL_mul_single
-- name    : GroundTheory.Automorphic.Whittaker.diag_mul_permGL_mul_single
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:35:18.759866+00:00
-- url     : https://prove2.me/theorems/15acffe8-1635-41fb-be12-af9c555ae09c
-- title:
--   Whittaker: diag mul perm GL mul single
-- statement:
--   The Whittaker construction uses the diag mul perm GL mul single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L405-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L405-L417

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (ψ₀ : AddChar F ℂ)

theorem GroundTheory.Automorphic.Whittaker.diag_mul_permGL_mul_single (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) (i j : Fin n)
    (a : F) :
    ((Iwasawa.diagGL F n t * permGL F w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        Matrix.single i j a = Matrix.single (w i) j ((t (w i) : F) * a) := by sorry
