-- Prove2me | Theorems.Thm_GlobalTheory_FibreLinInd_evalHom_appLE
-- name    : GlobalTheory.FibreLinInd.evalHom_appLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:41.176799+00:00
-- url     : https://prove2.me/theorems/328e062c-60e3-47a0-81fe-5f244a377125
-- title:
--   Fibre Lin Ind: eval Hom app LE
-- statement:
--   The Fibre Lin Ind construction uses the eval Hom app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenSetOfLinearIndependentOnFibres.lean#L107-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenSetOfLinearIndependentOnFibres.lean#L107-L112

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

theorem GlobalTheory.FibreLinInd.evalHom_appLE (h : Sp K ⟶ P) (U : P.Opens) (hU : ⊤ ≤ h ⁻¹ᵁ U) (π : P ⟶ G) (V : G.Opens)
    (hV : U ≤ π ⁻¹ᵁ V) (a : Γ(G, V)) :
    evalHom h U hU (π.appLE V U hV a) = valF (h ≫ π) V a := by sorry
