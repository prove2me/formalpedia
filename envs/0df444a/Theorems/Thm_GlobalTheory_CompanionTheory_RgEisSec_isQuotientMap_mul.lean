-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisSec_isQuotientMap_mul
-- name    : GlobalTheory.CompanionTheory.RgEisSec.isQuotientMap_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:59:39.580951+00:00
-- url     : https://prove2.me/theorems/46e3d3a2-2934-4869-9795-d0c97e35ea6b
-- title:
--   Rg Eis Sec: is Quotient Map mul
-- statement:
--   The Rg Eis Sec construction uses the is Quotient Map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SectionLawHolds.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SectionLawHolds.lean#L14-L17

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_Iwa
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SectionLawHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisSec
variable {G : Type} [Group G] [TopologicalSpace G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem GlobalTheory.CompanionTheory.RgEisSec.isQuotientMap_mul [IsTopologicalGroup G] {K P : Subgroup G} (hK : IsCompact (K : Set G))
    (hP : IsClosed (P : Set G)) (hI : Iwa P K) :
    Topology.IsQuotientMap (fun x : P × K => (x.1 : G) * (x.2 : G)) := by sorry
