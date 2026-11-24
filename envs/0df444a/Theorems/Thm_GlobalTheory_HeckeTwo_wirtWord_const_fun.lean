-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_wirtWord_const_fun
-- name    : GlobalTheory.HeckeTwo.wirtWord_const_fun
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:12:38.920047+00:00
-- url     : https://prove2.me/theorems/1b551765-153f-4728-90a6-359b1accc788
-- title:
--   Hecke Two: wirt Word const fun
-- statement:
--   The Hecke Two construction uses the wirt Word const fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothHolomorphicInSigmaFamilyOfSigmaOnly.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothHolomorphicInSigmaFamilyOfSigmaOnly.lean#L16-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyOfSigmaOnly
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
open GlobalTheory GlobalTheory.HeckeTwo

theorem GlobalTheory.HeckeTwo.wirtWord_const_fun {Φ : Type} [Fintype Φ] (ws : List (Φ × Bool)) (d : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord ws (fun _ : Φ → ℂ => d) = fun _ => if ws = [] then d else 0 := by sorry
