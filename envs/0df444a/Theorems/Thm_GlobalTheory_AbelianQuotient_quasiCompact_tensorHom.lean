-- Prove2me | Theorems.Thm_GlobalTheory_AbelianQuotient_quasiCompact_tensorHom
-- name    : GlobalTheory.AbelianQuotient.quasiCompact_tensorHom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:45.749128+00:00
-- url     : https://prove2.me/theorems/a9792b0f-e53e-423e-9ec1-b5eb30fd1287
-- title:
--   Abelian Quotient: quasi Compact tensor Hom
-- statement:
--   The Abelian Quotient construction uses the quasi Compact tensor Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuotientIsAbelianSchemeOfQuotientScheme.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuotientIsAbelianSchemeOfQuotientScheme.lean#L45-L48

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

theorem GlobalTheory.AbelianQuotient.quasiCompact_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : QuasiCompact f.left] [hg : QuasiCompact g.left] : QuasiCompact (f ⊗ₘ g).left := by sorry
