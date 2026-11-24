-- Prove2me | Theorems.Thm_GlobalTheory_Published_SvN_psi_sq
-- name    : GlobalTheory.Published.SvN.psi_sq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:58:12.50281+00:00
-- url     : https://prove2.me/theorems/a6019c83-a2e1-49c0-9f7c-f2924fe28ca8
-- title:
--   Sv N: psi sq
-- statement:
--   The Sv N construction uses the psi sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L421-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L421-L422

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
variable {W : Type} [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W}
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GlobalTheory.Published.SvN.psi_sq (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (t : F) : ψ (t / 2) ^ 2 = ψ t := by sorry
