-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OpenModelSections_nonzeroOnFibre_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections.nonzeroOnFibre_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:10:02.335874+00:00
-- url     : https://prove2.me/theorems/53cae65b-3d4e-408d-a255-362d2074783c
-- title:
--   Open Model Sections: nonzero On Fibre iff
-- statement:
--   The Open Model Sections construction uses the nonzero On Fibre iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/OpenModelSections.lean#L29-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/OpenModelSections.lean#L29-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoefficientFieldBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_OpenModelSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange
variable {X : Scheme.{0}} (G : Over X) (L : LB G.left)

theorem GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections.nonzeroOnFibre_iff {V : X.Opens} (θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)) (x : X)
    [IsReduced (Scheme.Hom.fiber G.hom x)] :
    NonzeroOnFibre G L θ x ↔ ∃ (i : L.ι) (g : G.left), G.hom g = x ∧ g ∈ G.left.basicOpen (θ i) := by sorry
