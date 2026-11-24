-- Prove2me | Theorems.Thm_GlobalTheory_submodule_fg_of_locally_le_fg
-- name    : GlobalTheory.submodule_fg_of_locally_le_fg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:21:51.652346+00:00
-- url     : https://prove2.me/theorems/a7df27c9-a061-4552-8df3-50a228125463
-- title:
--   Global Theory: submodule fg of locally le fg
-- statement:
--   The Global Theory construction uses the submodule fg of locally le fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubmoduleFgOfLocallyLeFg.lean#L5-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubmoduleFgOfLocallyLeFg.lean#L5-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubmoduleFgOfLocallyLeFg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.submodule_fg_of_locally_le_fg {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] (M : Submodule R A) (s : Set R) (hs : Ideal.span s = ⊤)
    (hE : ∀ g ∈ s, ∃ E : Finset A, ∀ b ∈ M, ∃ m : ℕ,
      algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A)) : M.FG := by sorry
