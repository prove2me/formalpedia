-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_SplitRep_isUnA_mix
-- name    : GlobalTheory.UnRep.SplitRep.isUnA_mix
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:24:38.404008+00:00
-- url     : https://prove2.me/theorems/b6351930-253f-4730-84a9-ef8fe323ab70
-- title:
--   Split Rep: is Un A mix
-- statement:
--   The Split Rep construction uses the is Un A mix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupport.lean#L51-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupport.lean#L51-L70

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
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem GlobalTheory.UnRep.SplitRep.isUnA_mix (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (ε : _root_.GlobalTheory.AdLat.RA F E) (hε : ε * ε = ε)
    (hs : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c ε = ε) (κ : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) (hκ : _root_.GlobalTheory.UnRep.IsUnA c G κ.1) :
    _root_.GlobalTheory.UnRep.IsUnA c G (_root_.GlobalTheory.UnRep.SplitRep.mix ε hε κ).1 := by sorry
