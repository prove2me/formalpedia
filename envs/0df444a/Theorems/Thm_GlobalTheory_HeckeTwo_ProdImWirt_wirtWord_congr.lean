-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_ProdImWirt_wirtWord_congr
-- name    : GlobalTheory.HeckeTwo.ProdImWirt.wirtWord_congr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:06:59.578302+00:00
-- url     : https://prove2.me/theorems/ebde1d79-00a3-493f-9d01-5b0da79af5d1
-- title:
--   Prod Im Wirt: wirt Word congr
-- statement:
--   The Prod Im Wirt construction uses the wirt Word congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdImIteratedWirtingerDerivWordDifferentiableOn.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdImIteratedWirtingerDerivWordDifferentiableOn.lean#L79-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdImIteratedWirtingerDerivWordDifferentiableOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.ProdImWirt
variable {Φ : Type} [Fintype Φ]

theorem GlobalTheory.HeckeTwo.ProdImWirt.wirtWord_congr {U : Set (Φ → ℂ)} (hU : IsOpen U) {f g : (Φ → ℂ) → ℂ} (h : Set.EqOn f g U)
    (w : List (Φ × Bool)) : Set.EqOn (wirtWord w f) (wirtWord w g) U := by sorry
