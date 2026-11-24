-- Prove2me | Theorems.Thm_GlobalTheory_CoverGlue_map_linComb
-- name    : GlobalTheory.CoverGlue.map_linComb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:27:43.555435+00:00
-- url     : https://prove2.me/theorems/19d2c10d-f26f-49a1-b9a9-c4da140d07ef
-- title:
--   Cover Glue: map lin Comb
-- statement:
--   The Cover Glue construction uses the map lin Comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionBasisGeometricFibresOfOpenCover.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionBasisGeometricFibresOfOpenCover.lean#L26-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionBasisGeometricFibresOfOpenCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverGlue

theorem GlobalTheory.CoverGlue.map_linComb {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {T : Over S} {T' : Over S'}
    (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (x : Fin n → (T' ⟶ G')) (c : Fin n → ℕ) :
    ρ (Out.linComb x c) = Out.linComb (fun l => ρ (x l)) c := by sorry
