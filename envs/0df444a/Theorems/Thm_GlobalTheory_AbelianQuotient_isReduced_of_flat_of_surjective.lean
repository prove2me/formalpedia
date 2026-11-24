-- Prove2me | Theorems.Thm_GlobalTheory_AbelianQuotient_isReduced_of_flat_of_surjective
-- name    : GlobalTheory.AbelianQuotient.isReduced_of_flat_of_surjective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:52:43.316795+00:00
-- url     : https://prove2.me/theorems/b134b6ef-1a5c-4bf0-bd50-f505a32c79d0
-- title:
--   Abelian Quotient: is Reduced of flat of surjective
-- statement:
--   The Abelian Quotient construction uses the is Reduced of flat of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuotientIsAbelianSchemeOfQuotientScheme.lean#L155-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuotientIsAbelianSchemeOfQuotientScheme.lean#L155-L161

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.AbelianQuotient
variable {S : Scheme.{0}}

theorem GlobalTheory.AbelianQuotient.isReduced_of_flat_of_surjective {X Y : Scheme.{0}} (p : X ⟶ Y) [Flat p] [Surjective p]
    [IsReduced X] : IsReduced Y := by sorry
