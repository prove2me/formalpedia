-- Prove2me | Theorems.Thm_GlobalTheory_MulFinite_pow_aux
-- name    : GlobalTheory.MulFinite.pow_aux
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:52.517905+00:00
-- url     : https://prove2.me/theorems/3160655b-92bf-4163-a2d7-48845c1a06e1
-- title:
--   Mul Finite: pow aux
-- statement:
--   The Mul Finite construction uses the pow aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomFromSpecResidueField.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomFromSpecResidueField.lean#L90-L96

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

theorem GlobalTheory.MulFinite.pow_aux {R : Type} [CommRing R] (g t : Rˣ) (x : R) (e N : ℕ) :
    ((g ^ N).val * x) ^ e * ((g ^ e * t)⁻¹).val ^ N = x ^ e * (t⁻¹).val ^ N := by sorry
