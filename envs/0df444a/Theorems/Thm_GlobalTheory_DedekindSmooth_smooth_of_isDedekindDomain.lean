-- Prove2me | Theorems.Thm_GlobalTheory_DedekindSmooth_smooth_of_isDedekindDomain
-- name    : GlobalTheory.DedekindSmooth.smooth_of_isDedekindDomain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:39.7136+00:00
-- url     : https://prove2.me/theorems/f08cf7f9-90b4-438b-98c4-f7547d090798
-- title:
--   Dedekind Smooth: smooth of is Dedekind Domain
-- statement:
--   The Dedekind Smooth construction uses the smooth of is Dedekind Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SmoothOfIsDedekindDomain.lean#L88-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SmoothOfIsDedekindDomain.lean#L88-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmoothOfIsDedekindDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DedekindSmooth
open Polynomial IsLocalRing

theorem GlobalTheory.DedekindSmooth.smooth_of_isDedekindDomain :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDedekindDomain B]
      [Algebra k B] [Algebra.FiniteType k B], Algebra.Smooth k B := by sorry
