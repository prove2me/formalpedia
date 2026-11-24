-- Prove2me | Theorems.Thm_GlobalTheory_PrescribedRank_htupW_eq
-- name    : GlobalTheory.PrescribedRank.htupW_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:54:37.479925+00:00
-- url     : https://prove2.me/theorems/806932c9-c129-489b-9df0-f0ab7cb1cb2e
-- title:
--   Prescribed Rank: htup W eq
-- statement:
--   The Prescribed Rank construction uses the htup W eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ConstMapInjective.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ConstMapInjective.lean#L46-L56

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ConstMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.G MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.PrescribedRank
variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

theorem GlobalTheory.PrescribedRank.htupW_eq (L : (noPlaces p O Kf).Tup) :
    (noPlaces p O Kf).HtupW L = Submodule.span O {1} := by sorry
