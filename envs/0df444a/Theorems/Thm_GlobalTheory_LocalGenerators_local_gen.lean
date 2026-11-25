-- Prove2me | Theorems.Thm_GlobalTheory_LocalGenerators_local_gen
-- name    : GlobalTheory.LocalGenerators.local_gen
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:52:26.252321+00:00
-- url     : https://prove2.me/theorems/18e95498-b955-4ee9-ac56-edd6644dcabc
-- title:
--   Local Generators: local gen
-- statement:
--   The Local Generators construction uses the local gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalGen.lean#L5-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalGen.lean#L5-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LocalGenerators

theorem GlobalTheory.LocalGenerators.local_gen {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : IsDedekindDomain.HeightOneSpectrum R) (J : Ideal R) (hJ : J ≠ ⊥) :
    ∃ d ∈ J, d ≠ (0 : R) ∧ ∃ s ∉ P.asIdeal, ∀ y ∈ J, ∃ o : R, s * y = o * d := by sorry
