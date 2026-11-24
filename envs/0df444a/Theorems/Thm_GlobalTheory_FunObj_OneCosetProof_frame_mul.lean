-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_frame_mul
-- name    : GlobalTheory.FunObj.OneCosetProof.frame_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:47.50632+00:00
-- url     : https://prove2.me/theorems/e036164a-02fb-4c91-8260-2b125a36fc1f
-- title:
--   One Coset Proof: frame mul
-- statement:
--   The One Coset Proof construction uses the frame mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L30-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L30-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]

theorem GlobalTheory.FunObj.OneCosetProof.frame_mul {a c b a' c' b' : ℕ} (h : a + c = b) (h' : a' + c' = b') (g : GL (Fin b) k) (g' : GL (Fin b') k)
    (X : Matrix (Fin a ⊕ Fin c) (Fin a' ⊕ Fin c') k) :
    (g⁻¹).val * X.reindex (frame h) (frame h') * g'.val =
      (((frameGL h g)⁻¹).val * X * (frameGL h' g').val).reindex (frame h) (frame h') := by sorry
