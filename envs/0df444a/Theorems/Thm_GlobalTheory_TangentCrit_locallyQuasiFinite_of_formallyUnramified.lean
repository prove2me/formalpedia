-- Prove2me | Theorems.Thm_GlobalTheory_TangentCrit_locallyQuasiFinite_of_formallyUnramified
-- name    : GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:08.345043+00:00
-- url     : https://prove2.me/theorems/24b1e9c3-eef0-4998-9533-a7f11b30db4e
-- title:
--   Tangent Crit: locally Quasi Finite of formally Unramified
-- statement:
--   The Tangent Crit construction uses the locally Quasi Finite of formally Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L200-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L200-L206

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.TangentCrit
open AlgebraicGeometry CategoryTheory Limits
universe u

theorem GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified {X Y : Scheme.{u}} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by sorry
