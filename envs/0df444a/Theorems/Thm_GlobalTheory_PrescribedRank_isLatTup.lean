-- Prove2me | Theorems.Thm_GlobalTheory_PrescribedRank_isLatTup
-- name    : GlobalTheory.PrescribedRank.isLatTup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:56.676339+00:00
-- url     : https://prove2.me/theorems/89d9c05a-f1f1-4d61-8bb4-96fca1e38d22
-- title:
--   Prescribed Rank: is Lat Tup
-- statement:
--   The Prescribed Rank construction uses the is Lat Tup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ConstMapInjective.lean#L36-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ConstMapInjective.lean#L36-L36

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

theorem GlobalTheory.PrescribedRank.isLatTup (L : (noPlaces p O Kf).Tup) : (noPlaces p O Kf).IsLatTup L := by sorry
