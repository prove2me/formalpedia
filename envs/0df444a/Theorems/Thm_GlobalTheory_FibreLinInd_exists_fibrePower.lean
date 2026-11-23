-- Prove2me | Theorems.Thm_GlobalTheory_FibreLinInd_exists_fibrePower
-- name    : GlobalTheory.FibreLinInd.exists_fibrePower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:46.234667+00:00
-- url     : https://prove2.me/theorems/b21ccb8c-4f28-4fce-90c4-f3d8b45d50ce
-- title:
--   Fibre Lin Ind: exists fibre Power
-- statement:
--   The Fibre Lin Ind construction uses the exists fibre Power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenSetOfLinearIndependentOnFibres.lean#L41-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenSetOfLinearIndependentOnFibres.lean#L41-L64

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

theorem GlobalTheory.FibreLinInd.exists_fibrePower {G Z : Scheme.{0}} (f : G ⟶ Z) [UniversallyOpen f]
    [LocallyOfFiniteType f] (r : ℕ) :
    ∃ (P : Scheme.{0}) (p : P ⟶ Z) (π : Fin r → (P ⟶ G)), UniversallyOpen p ∧
      LocallyOfFiniteType p ∧ (∀ k, π k ≫ f = p) ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ Z) (g : Fin r → (T ⟶ G)), (∀ k, g k ≫ f = x) →
        ∃ h : T ⟶ P, h ≫ p = x ∧ ∀ k, h ≫ π k = g k := by sorry
