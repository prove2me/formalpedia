-- Prove2me | Theorems.Thm_GlobalTheory_FlatBaseChangeIdeal_toImage_std
-- name    : GlobalTheory.FlatBaseChangeIdeal.toImage_std
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:31:29.712811+00:00
-- url     : https://prove2.me/theorems/8be45e84-3bdb-4719-811f-33b9a8c7e661
-- title:
--   Flat Base Change Ideal: to Image std
-- statement:
--   The Flat Base Change Ideal construction uses the to Image std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapFlat.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapComapFlat.lean#L9-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
open GlobalTheory GlobalTheory.FlatBaseChangeIdeal

theorem GlobalTheory.FlatBaseChangeIdeal.toImage_std {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by sorry
