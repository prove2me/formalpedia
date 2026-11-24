-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UniformizationBase_IsUnifBase_out
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase.IsUnifBase.out
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:16:26.24183+00:00
-- url     : https://prove2.me/theorems/de85a966-bbdf-4ad2-b9a5-306191f418eb
-- title:
--   Is Unif Base: out
-- statement:
--   The Is Unif Base construction uses the out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CoveringAndSmoothness.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/CoveringAndSmoothness.lean#L37-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAndSmoothness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase.IsUnifBase.out {Y : Model Xo c β} (h3 : Y.N3) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {ξ : Sp R ⟶ Y.X} (h : IsUnifBase Y R ξ) :
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), UniformisationConclusion t (ξ ⁻¹' abLocus Y.t.G) := by sorry
