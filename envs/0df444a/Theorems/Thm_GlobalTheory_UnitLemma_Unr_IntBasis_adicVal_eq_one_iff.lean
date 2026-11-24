-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_IntBasis_adicVal_eq_one_iff
-- name    : GlobalTheory.UnitLemma.Unr.IntBasis.adicVal_eq_one_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:34:02.08885+00:00
-- url     : https://prove2.me/theorems/0f726238-fdf9-4787-bce5-e747547dc411
-- title:
--   Int Basis: adic Val eq one iff
-- statement:
--   The Int Basis construction uses the adic Val eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralBasisUnramifiedInvolutionExt.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralBasisUnramifiedInvolutionExt.lean#L20-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.IntBasis
open IsLocalRing
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

theorem GlobalTheory.UnitLemma.Unr.IntBasis.adicVal_eq_one_iff (K : UQ) (a : K.O) : adicVal K (algebraMap K.O K.E a) = 1 ↔ IsUnit a := by sorry
