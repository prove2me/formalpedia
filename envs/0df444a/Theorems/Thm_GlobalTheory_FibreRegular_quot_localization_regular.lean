-- Prove2me | Theorems.Thm_GlobalTheory_FibreRegular_quot_localization_regular
-- name    : GlobalTheory.FibreRegular.quot_localization_regular
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:53.578248+00:00
-- url     : https://prove2.me/theorems/f37cb4a7-c4d0-44c7-b4de-9e94a42f94ed
-- title:
--   Fibre Regular: quot localization regular
-- statement:
--   The Fibre Regular construction uses the quot localization regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothFibreRegularLocalRing.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothFibreRegularLocalRing.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothFibreRegularLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.FibreRegular

theorem GlobalTheory.FibreRegular.quot_localization_regular (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (p : Ideal R) [p.IsPrime] (n : Ideal S) [n.IsPrime]
    (hn : n.comap (algebraMap R S) = p) :
    IsRegularLocalRing (Localization.AtPrime n ⧸
      (p.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime n))) := by sorry
