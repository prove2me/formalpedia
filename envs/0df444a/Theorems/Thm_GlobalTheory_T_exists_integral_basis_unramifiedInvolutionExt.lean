-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_integral_basis_unramifiedInvolutionExt
-- name    : GlobalTheory.T.exists_integral_basis_unramifiedInvolutionExt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:08.45337+00:00
-- url     : https://prove2.me/theorems/62f92b77-f310-45c5-9d9b-5e82364b07e0
-- title:
--   T: exists integral basis unramified Involution Ext
-- statement:
--   The T construction uses the exists integral basis unramified Involution Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralBasisUnramifiedInvolutionExtStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralBasisUnramifiedInvolutionExtStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_integral_basis_unramifiedInvolutionExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → letI : Algebra K.E K'.E := φ.toAlgebra; ∃ w : Module.Basis (Fin d) K.E K'.E, ∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k := by sorry
