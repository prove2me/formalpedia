-- Prove2me | Theorems.Thm_GlobalTheory_ExtUnique_intAct_unique_extension
-- name    : GlobalTheory.ExtUnique.intAct_unique_extension
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:09.889734+00:00
-- url     : https://prove2.me/theorems/6e4c8ffb-f7ac-4e2c-bfdb-e4d377a3cccf
-- title:
--   Ext Unique: int Act unique extension
-- statement:
--   The Ext Unique construction uses the int Act unique extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L257-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsSchemeTheoreticallyDominantSpecOfInjective.lean#L257-L262

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ExtUnique
variable {U S : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]

theorem GlobalTheory.ExtUnique.intAct_unique_extension (a : OAct ℤ (splitTorusAff (CommRingCat.of ℤ) ℤ))
    (ha : OAct.pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) _ a = intAct _) : a = intAct _ := by sorry
