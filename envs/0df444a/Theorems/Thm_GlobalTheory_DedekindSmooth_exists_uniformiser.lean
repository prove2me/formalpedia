-- Prove2me | Theorems.Thm_GlobalTheory_DedekindSmooth_exists_uniformiser
-- name    : GlobalTheory.DedekindSmooth.exists_uniformiser
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:35:29.281825+00:00
-- url     : https://prove2.me/theorems/ac7c1978-4d80-4c71-89de-814a3ec2a589
-- title:
--   Dedekind Smooth: exists uniformiser
-- statement:
--   The Dedekind Smooth construction uses the exists uniformiser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SmoothOfIsDedekindDomain.lean#L18-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SmoothOfIsDedekindDomain.lean#L18-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmoothOfIsDedekindDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DedekindSmooth
open Polynomial IsLocalRing

theorem GlobalTheory.DedekindSmooth.exists_uniformiser (B : Type) [CommRing B] [IsDedekindDomain B] (q : Ideal B) [q.IsPrime]
    (hq : q ≠ ⊥) : ∃ t ∈ q, t ≠ 0 ∧ maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap B (Localization.AtPrime q) t} := by sorry
