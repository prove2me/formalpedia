-- Prove2me | Theorems.Thm_GlobalTheory_FibreLinInd_top_le_iff
-- name    : GlobalTheory.FibreLinInd.top_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:55.836919+00:00
-- url     : https://prove2.me/theorems/90a590fd-0577-4fc9-b572-bf1e7fadd5be
-- title:
--   Fibre Lin Ind: top le iff
-- statement:
--   The Fibre Lin Ind construction uses the top le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenSetOfLinearIndependentOnFibres.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenSetOfLinearIndependentOnFibres.lean#L79-L82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenSetOfLinearIndependentOnFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FibreLinInd
variable {K : Type} [Field K] {P G : Scheme.{0}}

theorem GlobalTheory.FibreLinInd.top_le_iff (x : Sp K ⟶ P) (U : P.Opens) (z : Sp K) : ⊤ ≤ x ⁻¹ᵁ U ↔ x z ∈ U := by sorry
