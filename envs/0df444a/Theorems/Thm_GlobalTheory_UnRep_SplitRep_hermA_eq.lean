-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_SplitRep_hermA_eq
-- name    : GlobalTheory.UnRep.SplitRep.hermA_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:25:07.41495+00:00
-- url     : https://prove2.me/theorems/d351b1fc-e813-4f93-880f-ba2e2c55b96a
-- title:
--   Split Rep: herm A eq
-- statement:
--   The Split Rep construction uses the herm A eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupport.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupport.lean#L75-L77

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem GlobalTheory.UnRep.SplitRep.hermA_eq (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) :
    hermA c G x y = x ⬝ᵥ (fm F G *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by sorry
