-- Prove2me | Theorems.Thm_GlobalTheory_Published_JacquetShalikaLocalBound_exists_uniformizer
-- name    : GlobalTheory.Published.JacquetShalikaLocalBound.exists_uniformizer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:13.785064+00:00
-- url     : https://prove2.me/theorems/0a2a0115-e210-4680-b692-39f7c5a7f630
-- title:
--   Jacquet Shalika Local Bound: exists uniformizer
-- statement:
--   The Jacquet Shalika Local Bound construction uses the exists uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/NotIsGenericDetRepTwo.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/NotIsGenericDetRepTwo.lean#L43-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__NotIsGenericDetRepTwo_461173a5118a9903
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Whittaker
open GlobalTheory.Published.JacquetShalikaLocalBound
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.Published.JacquetShalikaLocalBound.exists_uniformizer : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by sorry
