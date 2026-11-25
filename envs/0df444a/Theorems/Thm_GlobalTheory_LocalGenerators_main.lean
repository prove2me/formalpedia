-- Prove2me | Theorems.Thm_GlobalTheory_LocalGenerators_main
-- name    : GlobalTheory.LocalGenerators.main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:39:59.115989+00:00
-- url     : https://prove2.me/theorems/65703db4-4798-4248-ab87-3ee5851a6590
-- title:
--   Local Generators: main
-- statement:
--   The Local Generators construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalGen.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalGen.lean#L33-L40

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

theorem GlobalTheory.LocalGenerators.main : ∀ {E : Type} [inst : Field E] [NumberField E]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (J : Ideal (NumberField.RingOfIntegers E)), J ≠ ⊥ →
    ∃ d ∈ J, d ≠ (0 : NumberField.RingOfIntegers E) ∧
      ∃ s ∉ IsDedekindDomain.HeightOneSpectrum.asIdeal P, ∀ y ∈ J,
        ∃ (o : NumberField.RingOfIntegers E), s * y = o * d := by sorry
