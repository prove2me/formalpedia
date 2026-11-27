-- Prove2me | Theorems.Thm_GlobalTheory_TorsionRepresent_exists_lift
-- name    : GlobalTheory.TorsionRepresent.exists_lift
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:28.633845+00:00
-- url     : https://prove2.me/theorems/dd85d09a-4bd5-4acf-ac09-5d643d174047
-- title:
--   Torsion Represent: exists lift
-- statement:
--   The Torsion Represent construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionFiniteFlatIff.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionFiniteFlatIff.lean#L32-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionFiniteFlatIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionRepresent
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (k : ℕ)

theorem GlobalTheory.TorsionRepresent.exists_lift {T : Over S} (x : T ⟶ G) (hx : x ^ k = 1) :
    ∃ y : T ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism.torsScheme G k, y ≫ incl G k = x := by sorry
