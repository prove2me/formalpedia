-- Prove2me | Theorems.Thm_GlobalTheory_QuadNormBase_exists_basis
-- name    : GlobalTheory.QuadNormBase.exists_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:35.633705+00:00
-- url     : https://prove2.me/theorems/e40750e2-c29a-4574-830f-793430a23874
-- title:
--   Quad Norm Base: exists basis
-- statement:
--   The Quad Norm Base construction uses the exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticExtNormFormOverAlgebra.lean#L21-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/QuadraticExtNormFormOverAlgebra.lean#L21-L64

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open GlobalTheory GlobalTheory.QuadNormBase

theorem GlobalTheory.QuadNormBase.exists_basis (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (hr : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    ∃ (δ : F) (b : Module.Basis (Fin 2) F E), ¬ IsSquare δ ∧ b 0 = 1 ∧ σ (b 1) = - b 1 ∧
      b 1 * b 1 = algebraMap F E δ := by sorry
