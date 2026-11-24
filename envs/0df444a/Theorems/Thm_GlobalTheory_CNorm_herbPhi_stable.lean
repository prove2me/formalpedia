-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_herbPhi_stable
-- name    : GlobalTheory.CNorm.herbPhi_stable
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:06:58.316163+00:00
-- url     : https://prove2.me/theorems/c372d40d-5928-4598-9831-e51a949ec5cc
-- title:
--   CNorm: herb Phi stable
-- statement:
--   The CNorm construction uses the herb Phi stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HerbrandPrimeOrder.lean#L34-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HerbrandPrimeOrder.lean#L34-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowPrimeRangeEqIteratedDifferenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionFiniteKerRangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormDifferenceIndexIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexRangeKerIterateEndomorphismStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
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

theorem GlobalTheory.CNorm.herbPhi_stable (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A) (hp : p.Prime)
    (C : Subgroup A) (hst : ∀ x ∈ C, σ x ∈ C) (hn : ∀ x ∈ C, nrm σ p x = 1)
    (hI : pIdx p C ≠ 0) (hT : pTor p C ≠ 0) :
    (C.map (dif σ)).relIndex C ≠ 0 ∧ Nat.card ↥(C ⊓ fix σ) ≠ 0 ∧
      pIdx p C * Nat.card ↥(C ⊓ fix σ) ^ (p - 1) =
        (C.map (dif σ)).relIndex C ^ (p - 1) * pTor p C := by sorry
