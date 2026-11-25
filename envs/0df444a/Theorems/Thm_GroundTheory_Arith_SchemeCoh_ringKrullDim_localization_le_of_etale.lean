-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ringKrullDim_localization_le_of_etale
-- name    : GroundTheory.Arith.SchemeCoh.ringKrullDim_localization_le_of_etale
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:24.451798+00:00
-- url     : https://prove2.me/theorems/dafd0bc4-80e9-4f05-aa4d-a99f719e704f
-- title:
--   Scheme Coh: ring Krull Dim localization le of etale
-- statement:
--   The Scheme Coh construction uses the ring Krull Dim localization le of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularCurve.lean#L38-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularCurve.lean#L38-L62

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing
universe u

theorem GroundTheory.Arith.SchemeCoh.ringKrullDim_localization_le_of_etale {P B : Type*} [CommRing P] [CommRing B]
    [Algebra P B] [Algebra.Etale P B] [IsRegularRing P] (Q : Ideal B) [Q.IsPrime] :
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (Localization.AtPrime (Q.under P)) := by sorry
