-- Prove2me | Theorems.Thm_GlobalTheory_PrescribedRank_range_constMap
-- name    : GlobalTheory.PrescribedRank.range_constMap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:54:41.338436+00:00
-- url     : https://prove2.me/theorems/187f9608-64b9-4888-a531-e9ee07921ab9
-- title:
--   Prescribed Rank: range const Map
-- statement:
--   The Prescribed Rank construction uses the range const Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ConstMapInjective.lean#L106-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ConstMapInjective.lean#L106-L120

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

theorem GlobalTheory.PrescribedRank.range_constMap (d : ℕ) :
    LinearMap.range (constMap p O Kf d) =
      Submodule.pi Set.univ fun _ : Fin d => (trivLevel p O Kf).funMod (noPlaces p O Kf).HtupW := by sorry
