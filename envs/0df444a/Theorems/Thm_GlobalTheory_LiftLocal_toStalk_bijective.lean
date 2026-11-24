-- Prove2me | Theorems.Thm_GlobalTheory_LiftLocal_toStalk_bijective
-- name    : GlobalTheory.LiftLocal.toStalk_bijective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:06:39.994591+00:00
-- url     : https://prove2.me/theorems/c77bb34c-a5f5-4c6f-aca2-67b231538440
-- title:
--   Lift Local: to Stalk bijective
-- statement:
--   The Lift Local construction uses the to Stalk bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftLocalPointAlongAffineFlatSurjection.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftLocalPointAlongAffineFlatSurjection.lean#L8-L19

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

theorem GlobalTheory.LiftLocal.toStalk_bijective (R : Type) [CommRing R] [IsLocalRing R] (q : PrimeSpectrum R)
    (hq : q = IsLocalRing.closedPoint R) : Function.Bijective (StructureSheaf.toStalk R q).hom := by sorry
