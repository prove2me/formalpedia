-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_fderiv_prod_coord
-- name    : GlobalTheory.HeckeTwo.fderiv_prod_coord
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:13:12.340891+00:00
-- url     : https://prove2.me/theorems/e9be406f-6a5d-4a31-aebe-2cec95b015d4
-- title:
--   Hecke Two: fderiv prod coord
-- statement:
--   The Hecke Two construction uses the fderiv prod coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeYDerivativeTermHasFDerivUpperHalfPlane.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeYDerivativeTermHasFDerivUpperHalfPlane.lean#L15-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermHasFDerivUpperHalfPlane
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
open Classical
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo

theorem GlobalTheory.HeckeTwo.fderiv_prod_coord {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → ℂ → ℂ) (L : ι → ℂ →L[ℝ] ℂ) (z : ι → ℂ)
    (hg : ∀ i, HasFDerivAt (g i) (L i) (z i)) :
    DifferentiableAt ℝ (fun w : ι → ℂ => ∏ i, g i (w i)) z ∧
    ∀ (j : ι) (v : ℂ), fderiv ℝ (fun w : ι → ℂ => ∏ i, g i (w i)) z (Pi.single j v) =
      L j v * ∏ i ∈ Finset.univ.erase j, g i (z i) := by sorry
