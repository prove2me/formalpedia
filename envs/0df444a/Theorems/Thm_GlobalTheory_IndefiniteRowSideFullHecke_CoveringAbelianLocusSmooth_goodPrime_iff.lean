-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CoveringAbelianLocusSmooth_goodPrime_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth.goodPrime_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:11.482615+00:00
-- url     : https://prove2.me/theorems/b1d45a7e-e765-4069-b0f1-d8bbafba08fe
-- title:
--   Covering Abelian Locus Smooth: good Prime iff
-- statement:
--   The Covering Abelian Locus Smooth construction uses the good Prime iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CoveringAbelianLocusSmooth.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CoveringAbelianLocusSmooth.lean#L61-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAbelianLocusSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth.goodPrime_iff (l : Level H) {p : ℕ} (hp : p.Prime) :
    GoodPrime l p ↔ ¬ (p : ℤ) ∣ discr E ∧ ¬ p ∣ l.M' := by sorry
