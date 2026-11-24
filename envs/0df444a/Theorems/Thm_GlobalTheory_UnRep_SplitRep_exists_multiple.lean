-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_SplitRep_exists_multiple
-- name    : GlobalTheory.UnRep.SplitRep.exists_multiple
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:26:12.833516+00:00
-- url     : https://prove2.me/theorems/e4741a70-0415-4a66-9736-61d4b715be4a
-- title:
--   Split Rep: exists multiple
-- statement:
--   The Split Rep construction uses the exists multiple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupport.lean#L86-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupport.lean#L86-L114

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
variable [NumberField E]
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
variable [NumberField E]

theorem GlobalTheory.UnRep.SplitRep.exists_multiple (s : 𝓞 E) (hs : s ≠ 0) :
    ∃ m : 𝓞 F, m ≠ 0 ∧ s ∣ algebraMap (𝓞 F) (𝓞 E) m ∧ ∀ v : HeightOneSpectrum (𝓞 F), m ∈ v.asIdeal →
      ∃ P : Ideal (𝓞 E), P.IsPrime ∧ s ∈ P ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by sorry
