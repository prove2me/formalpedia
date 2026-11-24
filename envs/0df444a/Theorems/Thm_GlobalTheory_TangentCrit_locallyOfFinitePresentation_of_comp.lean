-- Prove2me | Theorems.Thm_GlobalTheory_TangentCrit_locallyOfFinitePresentation_of_comp
-- name    : GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:03.691494+00:00
-- url     : https://prove2.me/theorems/38676098-7ea8-4a47-b042-6dc7c37264bf
-- title:
--   Tangent Crit: locally Of Finite Presentation of comp
-- statement:
--   The Tangent Crit construction uses the locally Of Finite Presentation of comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L182-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L182-L198

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

theorem GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S)
    [LocallyOfFinitePresentation (f ≫ π)] [LocallyOfFiniteType π] :
    LocallyOfFinitePresentation f := by sorry
