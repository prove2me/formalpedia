-- Prove2me | Theorems.Thm_GlobalTheory_FibreLinInd_isOpen_setOf_linearIndependent_on_fibres
-- name    : GlobalTheory.FibreLinInd.isOpen_setOf_linearIndependent_on_fibres
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:32.941892+00:00
-- url     : https://prove2.me/theorems/e6170f0f-0850-43f8-804e-a84c76873f22
-- title:
--   Fibre Lin Ind: is Open set Of linear Independent on fibres
-- statement:
--   The Fibre Lin Ind construction uses the is Open set Of linear Independent on fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenSetOfLinearIndependentOnFibres.lean#L114-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenSetOfLinearIndependentOnFibres.lean#L114-L183

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

theorem GlobalTheory.FibreLinInd.isOpen_setOf_linearIndependent_on_fibres :
    ∀ (G Z : Scheme.{0}) (f : G ⟶ Z) [Flat f] [LocallyOfFinitePresentation f] (L : LB G),
      L.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec L), IsOpen {z : Z | ∀ (K : Type) [Field K]
        [IsAlgClosed K] (x : Sp K ⟶ Z), Set.range x = {z} → ∀ c : Fin r → K,
          (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x →
            ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0} := by sorry
