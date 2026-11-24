-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_eq_one_of_cong
-- name    : GlobalTheory.CMVal.ValEx.eq_one_of_cong
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:13.273919+00:00
-- url     : https://prove2.me/theorems/766baab9-0792-47df-95f9-b5cc5ca62e5c
-- title:
--   Val Ex: eq one of cong
-- statement:
--   The Val Ex construction uses the eq one of cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L61-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L61-L114

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
variable {K : Type} [Field K] (v : Valuation K ℤᵐ⁰)

theorem GlobalTheory.CMVal.ValEx.eq_one_of_cong {l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (hv : v (l : K) = WithZero.exp (-1 : ℤ)) {z : Kˣ}
    (hz : IsOfFinOrder z) (h1 : z ∈ cong v 1) : z = 1 := by sorry
