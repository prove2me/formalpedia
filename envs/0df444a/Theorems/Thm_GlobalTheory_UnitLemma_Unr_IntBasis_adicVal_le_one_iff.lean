-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_IntBasis_adicVal_le_one_iff
-- name    : GlobalTheory.UnitLemma.Unr.IntBasis.adicVal_le_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:48.343507+00:00
-- url     : https://prove2.me/theorems/5bb8443e-1fbf-4d60-a9f4-c1ea1bbe76d8
-- title:
--   Int Basis: adic Val le one iff
-- statement:
--   The Int Basis construction uses the adic Val le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralBasisUnramifiedInvolutionExt.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralBasisUnramifiedInvolutionExt.lean#L16-L18

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

theorem GlobalTheory.UnitLemma.Unr.IntBasis.adicVal_le_one_iff (K : UQ) (x : K.E) : adicVal K x ≤ 1 ↔ ∃ a : K.O, algebraMap K.O K.E a = x := by sorry
