-- Prove2me | Theorems.Thm_GlobalTheory_GroupAlg_finite_of_finiteIndex
-- name    : GlobalTheory.GroupAlg.finite_of_finiteIndex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:37.931437+00:00
-- url     : https://prove2.me/theorems/75070bb3-7fc6-48d3-82a7-07cb81dc32a6
-- title:
--   Group Alg: finite of finite Index
-- statement:
--   The Group Alg construction uses the finite of finite Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinitePresentationOfInjective.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinitePresentationOfInjective.lean#L96-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.GroupAlg
variable (R : Type*) [CommRing R] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X)

theorem GlobalTheory.GroupAlg.finite_of_finiteIndex [u.range.FiniteIndex] : (mapDomainRingHom R u).Finite := by sorry
