-- Prove2me | Theorems.Thm_GlobalTheory_PrescribedRank_finClasses
-- name    : GlobalTheory.PrescribedRank.finClasses
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:55:40.822174+00:00
-- url     : https://prove2.me/theorems/c8b93133-5d5e-4336-9141-6c0cbf5543f5
-- title:
--   Prescribed Rank: fin Classes
-- statement:
--   The Prescribed Rank construction uses the fin Classes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ConstMapInjective.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ConstMapInjective.lean#L72-L74

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

theorem GlobalTheory.PrescribedRank.finClasses : (trivLevel p O Kf).FinClasses := by sorry
