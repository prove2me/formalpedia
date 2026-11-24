-- Prove2me | Theorems.Thm_GlobalTheory_isMonHom_of_fst_mul_snd
-- name    : GlobalTheory.isMonHom_of_fst_mul_snd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:58:22.921069+00:00
-- url     : https://prove2.me/theorems/8840302f-00b0-45ea-9216-f2588fb0308d
-- title:
--   Global Theory: is Mon Hom of fst mul snd
-- statement:
--   The Global Theory construction uses the is Mon Hom of fst mul snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GrpHomAlgebraisationOfReductions.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GrpHomAlgebraisationOfReductions.lean#L11-L24

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GrpHomAlgebraisationOfReductions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.isMonHom_of_fst_mul_snd {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (g : A ⟶ B)
    (h : (fst A A * snd A A) ≫ g = (fst A A ≫ g) * (snd A A ≫ g)) : IsMonHom g := by sorry
