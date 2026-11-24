-- Prove2me | Theorems.Thm_GlobalTheory_SmoothPointFamily_exists_basis_away
-- name    : GlobalTheory.SmoothPointFamily.exists_basis_away
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:19:34.013234+00:00
-- url     : https://prove2.me/theorems/a8bf0c1c-8a25-4a2b-bc5a-ab8bacf31072
-- title:
--   Smooth Point Family: exists basis away
-- statement:
--   The Smooth Point Family construction uses the exists basis away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsHolomorphicFamily.lean#L13-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsHolomorphicFamily.lean#L13-L48

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
set_option backward.isDefEq.respectTransparency.types false

theorem GlobalTheory.SmoothPointFamily.exists_basis_away {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] :
    ∃ (g : S) (m : ℕ) (s : Fin m → S)
      (b : Module.Basis (Fin m) (Localization.Away g) Ω[Localization.Away g⁄R]),
      g ∉ p ∧ ∀ i, b i = D R (Localization.Away g) (algebraMap S _ (s i)) := by sorry
