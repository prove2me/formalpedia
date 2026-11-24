-- Prove2me | Theorems.Thm_GlobalTheory_comul_one_tmul_eq_distribBaseChange
-- name    : GlobalTheory.comul_one_tmul_eq_distribBaseChange
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:12.826861+00:00
-- url     : https://prove2.me/theorems/19e32c84-b518-4cd6-a51d-f171963eac71
-- title:
--   Global Theory: comul one tmul eq distrib Base Change
-- statement:
--   The Global Theory construction uses the comul one tmul eq distrib Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueAlgEquivOfCompatibleQuotient.lean#L187-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueAlgEquivOfCompatibleQuotient.lean#L187-L195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct
variable {R : Type*} [CommRing R] (I : Ideal R)
variable [IsNoetherianRing R] [IsAdicComplete I R]
omit [IsNoetherianRing R] [IsAdicComplete I R]

theorem GlobalTheory.comul_one_tmul_eq_distribBaseChange (S : Type*) [CommRing S] [Algebra R S] {A : Type*}
    [AddCommGroup A] [Module R A] [Coalgebra R A] (a : A) :
    Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[R] a) =
      AlgebraTensorModule.distribBaseChange R S A A (1 ⊗ₜ Coalgebra.comul a) := by sorry
