-- Prove2me | Theorems.Thm_GlobalTheory_OpenDim_topologicalKrullDim_open
-- name    : GlobalTheory.OpenDim.topologicalKrullDim_open
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:03:20.887281+00:00
-- url     : https://prove2.me/theorems/9aadf4b5-1cb9-41d4-9b40-18d7925015c3
-- title:
--   Open Dim: topological Krull Dim open
-- statement:
--   The Open Dim construction uses the topological Krull Dim open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimEqOfIsIsoRestrict.lean#L43-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimEqOfIsIsoRestrict.lean#L43-L72

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfIsIsoRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OpenDim

theorem GlobalTheory.OpenDim.topologicalKrullDim_open (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (f : Y ⟶ Sp F) [LocallyOfFiniteType f] (V : Y.Opens) (hne : (V : Set Y).Nonempty) :
    topologicalKrullDim (V : Set Y) = topologicalKrullDim Y := by sorry
