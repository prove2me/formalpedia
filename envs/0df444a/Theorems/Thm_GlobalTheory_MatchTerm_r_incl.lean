-- Prove2me | Theorems.Thm_GlobalTheory_MatchTerm_r_incl
-- name    : GlobalTheory.MatchTerm.r_incl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:29.99881+00:00
-- url     : https://prove2.me/theorems/fdbe71a7-86b4-4b9f-8e00-5d1ba9c26564
-- title:
--   Match Term: r incl
-- statement:
--   The Match Term construction uses the r incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaMatchingExistsRightTorusTorsion.lean#L128-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaMatchingExistsRightTorusTorsion.lean#L128-L132

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
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)

theorem GlobalTheory.MatchTerm.r_incl {k K : ℕ} (k' : ℕ) (hK : K = k * k') (hk : k' ≠ 0) {p : N.QT k} {p' : N'.QT k} {q : N.QT K}
    {q' : N'.QT K} (h1 : q.1.1 = p.1.1 ^ k') (h2 : q.1.2 = p.1.2) (h3 : q'.1.1 = p'.1.1 ^ k')
    (h4 : q'.1.2 = p'.1.2) : μ.r k p p' ↔ μ.r K q q' := by sorry
