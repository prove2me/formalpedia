-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_LatBij_exists_equiv
-- name    : GlobalTheory.CMVal.LatBij.exists_equiv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:04:47.782016+00:00
-- url     : https://prove2.me/theorems/d7017074-ed76-493c-9691-1ac3978b9996
-- title:
--   Lat Bij: exists equiv
-- statement:
--   The Lat Bij construction uses the exists equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLatticePointsIntegralIdelesEquiv.lean#L90-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLatticePointsIntegralIdelesEquiv.lean#L90-L100

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLatticePointsIntegralIdelesEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.LatBij
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.LatBij.exists_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)), IsBaseCond 𝔣 → 𝔣 ∣ c → c ≠ ⊥ →
    ∃ e : (Σ q : PicO c, modUnits (lattice c q.out)) ≃
      {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c},
      ∀ p, ∀ y : (Af E)ˣ, (y : Af E) = algebraMap E (Af E) (p.2.1.out) * (((Quotient.out p.1 : (Af E)ˣ)⁻¹ : (Af E)ˣ) : Af E) →
        (e p).1 = QuotientGroup.mk y := by sorry
