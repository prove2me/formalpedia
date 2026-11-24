-- Prove2me | Theorems.Thm_GlobalTheory_FinTypCount_cong_of_code
-- name    : GlobalTheory.FinTypCount.cong_of_code
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:26:01.121018+00:00
-- url     : https://prove2.me/theorems/5875f58a-1936-4135-8657-71c1c016aca3
-- title:
--   Fin Typ Count: cong of code
-- statement:
--   The Fin Typ Count construction uses the cong of code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelic.lean#L90-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelic.lean#L90-L133

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

theorem GlobalTheory.FinTypCount.cong_of_code {N m : ℕ} {c : Fin n → Fin n → L} {g g' : GAf L n}
    (hg : ∀ i j, (m : AL L) * (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L)
    (e : ∀ i j, ∃ y ∈ ALint L, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
      c i j ⊗ₜ[L⁺] (1 : AFplus L) + (m * N) • y)
    (e' : ∀ i j, ∃ y ∈ ALint L, (g'.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
      c i j ⊗ₜ[L⁺] (1 : AFplus L) + (m * N) • y) :
    Cong L n N (g⁻¹ * g') := by sorry
