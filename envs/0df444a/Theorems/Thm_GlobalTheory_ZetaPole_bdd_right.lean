-- Prove2me | Theorems.Thm_GlobalTheory_ZetaPole_bdd_right
-- name    : GlobalTheory.ZetaPole.bdd_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:02.370452+00:00
-- url     : https://prove2.me/theorems/86c80552-c150-4174-a424-26894c5d8a8f
-- title:
--   Zeta Pole: bdd right
-- statement:
--   The Zeta Pole construction uses the bdd right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PartialZetaTotallyRealAtMostSimplePole.lean#L122-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PartialZetaTotallyRealAtMostSimplePole.lean#L122-L140

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

theorem GlobalTheory.ZetaPole.bdd_right (F : Type) [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ)
    (hZ : IsPartialZeta C Z) : ∃ B : ℝ, ∀ᶠ x : ℝ in 𝓝[>] 1, ‖((x : ℂ) - 1) * Z x‖ ≤ B := by sorry
