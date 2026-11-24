-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TopGroup_finite_image_of_right_invariant_near_one
-- name    : GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:16:26.374919+00:00
-- url     : https://prove2.me/theorems/d5482f0c-1fda-4776-98b0-eaae89ae9104
-- title:
--   Top Group: finite image of right invariant near one
-- statement:
--   The Top Group construction uses the finite image of right invariant near one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteImageCompactRightInvariant.lean#L5-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteImageCompactRightInvariant.lean#L5-L24

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteImageCompactRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TopGroup

theorem GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one :
    ∀ {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Set Γ),
      IsCompact K → ∀ Gf : Γ → X, {s : Γ | ∀ x, Gf (x * s) = Gf x} ∈ nhds (1 : Γ) →
        (Gf '' K).Finite := by sorry
