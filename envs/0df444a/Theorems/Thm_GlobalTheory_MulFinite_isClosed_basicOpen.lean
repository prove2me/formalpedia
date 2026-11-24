-- Prove2me | Theorems.Thm_GlobalTheory_MulFinite_isClosed_basicOpen
-- name    : GlobalTheory.MulFinite.isClosed_basicOpen
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:28:16.379153+00:00
-- url     : https://prove2.me/theorems/e110cb35-16b5-4104-a3cd-3b2f1c7672eb
-- title:
--   Mul Finite: is Closed basic Open
-- statement:
--   The Mul Finite construction uses the is Closed basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomFromSpecResidueField.lean#L29-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomFromSpecResidueField.lean#L29-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
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
noncomputable section
open GlobalTheory GlobalTheory.MulFinite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace Polynomial

theorem GlobalTheory.MulFinite.isClosed_basicOpen {Z : Scheme.{0}} {K : Type} [Field K] (f : Z ⟶ Spec (.of K))
    [UniversallyClosed f] (a : Γ(Z, ⊤)) : IsClosed (Z.basicOpen a : Set Z) := by sorry
