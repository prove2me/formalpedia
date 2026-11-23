-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_IntBasis_adicVal_map
-- name    : GlobalTheory.UnitLemma.Unr.IntBasis.adicVal_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:29.161895+00:00
-- url     : https://prove2.me/theorems/d27ba45a-71d2-4dd4-a8da-a497f71756ae
-- title:
--   Int Basis: adic Val map
-- statement:
--   The Int Basis construction uses the adic Val map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralBasisUnramifiedInvolutionExt.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralBasisUnramifiedInvolutionExt.lean#L24-L34

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

theorem GlobalTheory.UnitLemma.Unr.IntBasis.adicVal_map (h : IsUnrExt K K' d φ) (x : K.E) : adicVal K' (φ x) = adicVal K x := by sorry
