-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SymplecticBasisLevel_incl_over
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel.incl_over
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:25.7248+00:00
-- url     : https://prove2.me/theorems/154cdd0d-9fe0-5415-82bc-c24d3a11d528
-- title:
--   Symplectic Basis Level: incl over
-- statement:
--   The Symplectic Basis Level construction uses the incl over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/SymplecticBasisLevel.lean#L141-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/SymplecticBasisLevel.lean#L141-L141

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_SymplecticBasisLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel.incl_over (l : Level H) : (KA l).val.toRingHom (baseKA l).ρ = H.rt0 := by sorry
