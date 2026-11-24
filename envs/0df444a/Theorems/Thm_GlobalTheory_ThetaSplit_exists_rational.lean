-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSplit_exists_rational
-- name    : GlobalTheory.ThetaSplit.exists_rational
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:07:37.731378+00:00
-- url     : https://prove2.me/theorems/3f83aaf3-a9b1-4921-ad0c-26bd592da241
-- title:
--   Theta Split: exists rational
-- statement:
--   The Theta Split construction uses the exists rational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LbPowDescendsOfIsotropic.lean#L77-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LbPowDescendsOfIsotropic.lean#L77-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescendsOfIsotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ThetaSplit

theorem GlobalTheory.ThetaSplit.exists_rational {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] {X : Scheme.{0}} (f : X ⟶ Sp k)
    [IsFinite f] (y : Sp k' ⟶ X) : ∃ c : Sp k ⟶ X, c ≫ f = 𝟙 _ ∧ (y ≫ f) ≫ c = y := by sorry
