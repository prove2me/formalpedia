-- Prove2me | Theorems.Thm_GlobalTheory_FinTypCount_exists_code
-- name    : GlobalTheory.FinTypCount.exists_code
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:26:03.35306+00:00
-- url     : https://prove2.me/theorems/f9970898-08ab-4357-a27a-70a711be0686
-- title:
--   Fin Typ Count: exists code
-- statement:
--   The Fin Typ Count construction uses the exists code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelic.lean#L73-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelic.lean#L73-L81

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.FinTypCount
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
variable {n : ℕ}

theorem GlobalTheory.FinTypCount.exists_code (N : ℕ) (hN : 0 < N) (g : GAf L n) :
    ∃ p : ℕ × (Fin n → Fin n → L), 0 < p.1 ∧
      (∀ i j, (p.1 : AL L) * (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L) ∧
      ∀ i j, ∃ y ∈ ALint L, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        p.2 i j ⊗ₜ[L⁺] (1 : AFplus L) + (p.1 * N) • y := by sorry
