-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EpsilonPointMorphisms_Unif_exists_chart
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Unif.exists_chart
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:14:16.75398+00:00
-- url     : https://prove2.me/theorems/1060b1a0-9b8d-4336-b0b4-7b2b628bf9e1
-- title:
--   Unif: exists chart
-- statement:
--   The Unif construction uses the exists chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/ExponentialDifferential.lean#L166-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/ExponentialDifferential.lean#L166-L173

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_ExponentialDifferential
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms
open GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Unif
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (F : Unif A L g)

theorem GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Unif.exists_chart (z : Fin g → ℂ) : ∃ i, z ∈ pre F.exp (L.U i) := by sorry
