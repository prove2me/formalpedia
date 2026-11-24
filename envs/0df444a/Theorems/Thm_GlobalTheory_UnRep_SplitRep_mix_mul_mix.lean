-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_SplitRep_mix_mul_mix
-- name    : GlobalTheory.UnRep.SplitRep.mix_mul_mix
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:23:34.74236+00:00
-- url     : https://prove2.me/theorems/1175444f-7598-4978-91bb-7353d2e9e612
-- title:
--   Split Rep: mix mul mix
-- statement:
--   The Split Rep construction uses the mix mul mix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupport.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupport.lean#L39-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryAdelicDecompositionSplitSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.SplitRep
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix

theorem GlobalTheory.UnRep.SplitRep.mix_mul_mix {R : Type} [CommRing R] {n : ℕ} (ε : R) (hε : ε * ε = ε)
    (hε' : (1 - ε) * (1 - ε) = 1 - ε) (κ : GL (Fin n) R) :
    (_root_.GlobalTheory.UnRep.SplitRep.mix ε hε κ).1 * (_root_.GlobalTheory.UnRep.SplitRep.mix (1 - ε) hε' κ).1 = κ.1 := by sorry
