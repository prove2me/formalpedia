-- Prove2me | Theorems.Thm_GlobalTheory_ZetaPole_norm_le_idealZetaR
-- name    : GlobalTheory.ZetaPole.norm_le_idealZetaR
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:15.912145+00:00
-- url     : https://prove2.me/theorems/d85a09c7-94f7-4db0-b5c0-e89dffdfa90a
-- title:
--   Zeta Pole: norm le ideal Zeta R
-- statement:
--   The Zeta Pole construction uses the norm le ideal Zeta R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PartialZetaTotallyRealAtMostSimplePole.lean#L96-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PartialZetaTotallyRealAtMostSimplePole.lean#L96-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialZetaTotallyRealAtMostSimplePole
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex Filter Topology
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.ZetaPole

theorem GlobalTheory.ZetaPole.norm_le_idealZetaR (F : Type) [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ)
    (hZ : IsPartialZeta C Z) {x : ℝ} (hx : 1 < x) : ‖Z x‖ ≤ ReciprocityTheory.Cheb.idealZetaR F x := by sorry
