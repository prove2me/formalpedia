-- Prove2me | Theorems.Thm_GlobalTheory_Published_SvN_isCompact_int
-- name    : GlobalTheory.Published.SvN.isCompact_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:03.893183+00:00
-- url     : https://prove2.me/theorems/22d50b87-78c6-4a49-b90f-7f89b9a2bf72
-- title:
--   Sv N: is Compact int
-- statement:
--   The Sv N construction uses the is Compact int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L384-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L384-L384

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GlobalTheory.Published.SvN.isCompact_int : IsCompact (𝒪[F] : Set F) := by sorry
