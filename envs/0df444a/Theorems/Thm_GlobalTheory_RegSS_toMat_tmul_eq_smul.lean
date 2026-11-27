-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_toMat_tmul_eq_smul
-- name    : GlobalTheory.RegSS.toMat_tmul_eq_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T06:21:00.295466+00:00
-- url     : https://prove2.me/theorems/42a9980e-046a-484c-9987-c8e07e72c7e7
-- title:
--   Reg SS: to Mat tmul eq smul
-- statement:
--   The Reg SS construction uses the to Mat tmul eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorCommutant.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorCommutant.lean#L70-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleTensorCommutant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS

theorem GlobalTheory.RegSS.toMat_tmul_eq_smul {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type}
    [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (l : plusAlg σ J γ) (a : E ⊗[F] R) :
    toMat σ J γ R (l ⊗ₜ a) = a • ((l : genAlg γ) : Matrix n n E).map (inclE (F := F) R) := by sorry
