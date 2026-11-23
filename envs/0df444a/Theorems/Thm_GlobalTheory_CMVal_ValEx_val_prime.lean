-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_val_prime
-- name    : GlobalTheory.CMVal.ValEx.val_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:49.001861+00:00
-- url     : https://prove2.me/theorems/6dfbde75-6aab-4797-8553-fe250d1a871e
-- title:
--   Val Ex: val prime
-- statement:
--   The Val Ex construction uses the val prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L169-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L169-L189

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

theorem GlobalTheory.CMVal.ValEx.val_prime {l : ℕ} (hl : l.Prime) (hd : ¬ (l : ℤ) ∣ discr E) (w : HeightOneSpectrum (𝓞 E))
    (hw : (l : 𝓞 E) ∈ w.asIdeal) : w.valuation E (l : E) = WithZero.exp (-1 : ℤ) := by sorry
