-- Prove2me | Theorems.Thm_GlobalTheory_TorsionRepresent_comp_incl_pow
-- name    : GlobalTheory.TorsionRepresent.comp_incl_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:34.516584+00:00
-- url     : https://prove2.me/theorems/a8726dcf-e299-448f-bd65-3f635ed2bac2
-- title:
--   Torsion Represent: comp incl pow
-- statement:
--   The Torsion Represent construction uses the comp incl pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionFiniteFlatIff.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionFiniteFlatIff.lean#L23-L30

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

theorem GlobalTheory.TorsionRepresent.comp_incl_pow {T : Over S} (y : T ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism.torsScheme G k) : (y ≫ incl G k) ^ k = 1 := by sorry
