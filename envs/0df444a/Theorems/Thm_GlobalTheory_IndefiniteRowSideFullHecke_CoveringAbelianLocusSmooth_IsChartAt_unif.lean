-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CoveringAbelianLocusSmooth_IsChartAt_unif
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth.IsChartAt.unif
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:10:25.819938+00:00
-- url     : https://prove2.me/theorems/af9a0478-b3a4-5257-ae73-301cc0d3e1f7
-- title:
--   Is Chart At: unif
-- statement:
--   The Is Chart At construction uses the unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CoveringAbelianLocusSmooth.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CoveringAbelianLocusSmooth.lean#L38-L42

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
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth.IsChartAt.unif {Y : Model Xo c β} (hY : Y.N3) {x : Y.X} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {ξ : Sp R ⟶ Y.X} (h : IsChartAt Y x R ξ) :
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), UniformisationConclusion t (ξ ⁻¹' abLocus Y.t.G) := by sorry
