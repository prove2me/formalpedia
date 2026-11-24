-- Prove2me | Theorems.Thm_GlobalTheory_LiftLocal_isLocalHom_of_bijective
-- name    : GlobalTheory.LiftLocal.isLocalHom_of_bijective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:06:16.810833+00:00
-- url     : https://prove2.me/theorems/fe912bcf-4655-4b9d-9a01-49b5d8945e35
-- title:
--   Lift Local: is Local Hom of bijective
-- statement:
--   The Lift Local construction uses the is Local Hom of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftLocalPointAlongAffineFlatSurjection.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftLocalPointAlongAffineFlatSurjection.lean#L21-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SRelOneOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftLocalPointAlongAffineFlatSurjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LiftLocal

theorem GlobalTheory.LiftLocal.isLocalHom_of_bijective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Bijective f) : IsLocalHom f := by sorry
