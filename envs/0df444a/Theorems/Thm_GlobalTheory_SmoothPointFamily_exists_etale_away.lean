-- Prove2me | Theorems.Thm_GlobalTheory_SmoothPointFamily_exists_etale_away
-- name    : GlobalTheory.SmoothPointFamily.exists_etale_away
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:19:29.682815+00:00
-- url     : https://prove2.me/theorems/4170c3c1-29fb-4d44-9bc5-7bbe1f797972
-- title:
--   Smooth Point Family: exists etale away
-- statement:
--   The Smooth Point Family construction uses the exists etale away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsHolomorphicFamily.lean#L50-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsHolomorphicFamily.lean#L50-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolomorphicSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsHolomorphicFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory GlobalTheory.SmoothPointFamily
open KaehlerDifferential

theorem GlobalTheory.SmoothPointFamily.exists_etale_away {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] :
    ∃ (g : S) (m : ℕ) (s : Fin m → S), g ∉ p ∧
      (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away g))
        fun i => algebraMap S (Localization.Away g) (s i)).Etale := by sorry
