-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_exists_locChar
-- name    : GlobalTheory.CMVal.ValEx.exists_locChar
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:45.437239+00:00
-- url     : https://prove2.me/theorems/8fbe7664-fd5f-4dc3-bb6e-4384e44f1333
-- title:
--   Val Ex: exists loc Char
-- statement:
--   The Val Ex construction uses the exists loc Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L197-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L197-L255

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.ValEx.exists_locChar {l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (w : HeightOneSpectrum (𝓞 E))
    (hv : w.valuation E (l : E) = WithZero.exp (-1 : ℤ)) (θ : Eˣ →* ℂˣ)
    (u : Eˣ) (hu : (u : E) = 1 + l) :
    ∃ ch : (w.adicCompletion E)ˣ →* ℂˣ, Continuous ch ∧ (∀ x, ‖((ch x : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ x ∈ cong (Valued.v : Valuation (w.adicCompletion E) ℤᵐ⁰) 2, ch x = 1) ∧
      (∀ z, IsOfFinOrder z → ch (toLoc w z) = θ z) ∧ ch (toLoc w u) ≠ 1 := by sorry
