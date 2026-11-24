-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_basis_trace_conj_unit
-- name    : GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:37:08.499271+00:00
-- url     : https://prove2.me/theorems/98ae9f74-b61d-4ec1-8fb8-15f3f5e9d592
-- title:
--   Unr: exists basis trace conj unit
-- statement:
--   The Unr construction uses the exists basis trace conj unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBasisTraceInvolutionDetUnitUnramified.lean#L10-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBasisTraceInvolutionDetUnitUnramified.lean#L10-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniformizerCompatibleUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitTraceFormDiscrUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitDetConjugationMatrixIntegralBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBasisTraceInvolutionDetUnitUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → letI : Algebra K.E K'.E := φ.toAlgebra; ∃ w : Module.Basis (Fin d) K.E K'.E, (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det ≠ 0 ∧ val K.O (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = 0 := by sorry
