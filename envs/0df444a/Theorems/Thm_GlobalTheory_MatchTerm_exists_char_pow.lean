-- Prove2me | Theorems.Thm_GlobalTheory_MatchTerm_exists_char_pow
-- name    : GlobalTheory.MatchTerm.exists_char_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:06:11.860492+00:00
-- url     : https://prove2.me/theorems/fafa8120-d264-4252-aa8b-53aea73e0b49
-- title:
--   Match Term: exists char pow
-- statement:
--   The Match Term construction uses the exists char pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaMatchingExistsRightTorusTorsion.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaMatchingExistsRightTorusTorsion.lean#L11-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Module Filter
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.MatchTerm

theorem GlobalTheory.MatchTerm.exists_char_pow {K X : Type} [Field K] [IsAlgClosed K] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {k : ℕ} (hk : k ≠ 0) (t : Multiplicative X →* Kˣ) :
    ∃ s : Multiplicative X →* Kˣ, s ^ k = t := by sorry
