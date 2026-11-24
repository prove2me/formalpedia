-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_pIdx_of_ker_eq_range
-- name    : GlobalTheory.CNorm.pIdx_of_ker_eq_range
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:28:18.213525+00:00
-- url     : https://prove2.me/theorems/afd86153-a3bd-4051-8d47-5059fcb5ab97
-- title:
--   CNorm: p Idx of ker eq range
-- statement:
--   The CNorm construction uses the p Idx of ker eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/PIdxUnitsFiniteExtensionAdicCompletion.lean#L70-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/PIdxUnitsFiniteExtensionAdicCompletion.lean#L70-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexTopOfGroupFg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CardQuotSpanAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteSpanAlgebraMapOfFreeFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormCoeffMinpolyLeOneOfNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexUnitsOfIsAdicCompleteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm

theorem GlobalTheory.CNorm.pIdx_of_ker_eq_range (p : ℕ) (hp : 0 < p) {A B : Type} [CommGroup A] [CommGroup B]
    (j : A →* B) (hj : Function.Injective j) (g : B →* Multiplicative ℤ) (hk : g.ker = j.range)
    (hg : g.range ≠ ⊥) (N : ℕ) (hN : N ≠ 0) (h1 : pTor p (⊤ : Subgroup A) ≠ 0)
    (h2 : pIdx p (⊤ : Subgroup A) = N * pTor p (⊤ : Subgroup A)) :
    pTor p (⊤ : Subgroup B) ≠ 0 ∧ pIdx p (⊤ : Subgroup B) = p * N * pTor p (⊤ : Subgroup B) := by sorry
