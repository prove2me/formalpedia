-- Prove2me | Theorems.Thm_GlobalTheory_FormalAlg_baseIdeal_ideal
-- name    : GlobalTheory.FormalAlg.baseIdeal_ideal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:29.638305+00:00
-- url     : https://prove2.me/theorems/a48a20a8-be92-4d46-8b5f-255ac3eda6f1
-- title:
--   Formal Alg: base Ideal ideal
-- statement:
--   The Formal Alg construction uses the base Ideal ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BaseIdealIdeal.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BaseIdealIdeal.lean#L19-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.FormalAlg
variable {R : Type} [CommRing R] {W : Scheme.{0}}

theorem GlobalTheory.FormalAlg.baseIdeal_ideal (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (U : W.affineOpens) :
    (baseIdeal f J).ideal U = J.map (cst f U.1) := by sorry
