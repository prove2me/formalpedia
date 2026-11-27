-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_complexComponent_eq_one_of_isOfFinOrder
-- name    : GroundTheory.Global.HeckeCharacter.complexComponent_eq_one_of_isOfFinOrder
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:22.840094+00:00
-- url     : https://prove2.me/theorems/2fa4e235-01f6-4feb-837a-8327f3625ea5
-- title:
--   Hecke Character: complex Component eq one of is Of Fin Order
-- statement:
--   The Hecke Character construction uses the complex Component eq one of is Of Fin Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteOrderParams.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteOrderParams.lean#L36-L46

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

theorem GroundTheory.Global.HeckeCharacter.complexComponent_eq_one_of_isOfFinOrder (h : IsOfFinOrder χ) {w : InfinitePlace K}
    (hw : w.IsComplex) (z : ℂˣ) : χ.complexComponent hw z = 1 := by sorry
