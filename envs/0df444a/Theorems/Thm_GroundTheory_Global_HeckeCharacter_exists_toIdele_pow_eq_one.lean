-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_exists_toIdele_pow_eq_one
-- name    : GroundTheory.Global.HeckeCharacter.exists_toIdele_pow_eq_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:14.629072+00:00
-- url     : https://prove2.me/theorems/a46e27a9-5ce4-473a-acab-f60a931d8736
-- title:
--   Hecke Character: exists to Idele pow eq one
-- statement:
--   The Hecke Character construction uses the exists to Idele pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteOrderParams.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteOrderParams.lean#L20-L25

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteOrderParams
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.HeckeCharacter
open IdeleGroup
variable (χ : HeckeCharacter K)

theorem GroundTheory.Global.HeckeCharacter.exists_toIdele_pow_eq_one (h : IsOfFinOrder χ) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : IdeleGroup K, χ.toIdele x ^ n = 1 := by sorry
