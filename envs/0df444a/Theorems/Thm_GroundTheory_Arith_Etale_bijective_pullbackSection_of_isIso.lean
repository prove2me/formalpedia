-- Prove2me | Theorems.Thm_GroundTheory_Arith_Etale_bijective_pullbackSection_of_isIso
-- name    : GroundTheory.Arith.Etale.bijective_pullbackSection_of_isIso
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:26:13.047817+00:00
-- url     : https://prove2.me/theorems/f57bd9c8-ed75-4fac-8f2a-9de5e6412cf4
-- title:
--   Etale: bijective pullback Section of is Iso
-- statement:
--   The Etale construction uses the bijective pullback Section of is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L168-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L168-L187

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u

theorem GroundTheory.Arith.Etale.bijective_pullbackSection_of_isIso {T U : Scheme.{u}} (g : T ⟶ U) [IsIso g] (N : U.Modules) :
    Function.Bijective (pullbackSection g N) := by sorry
